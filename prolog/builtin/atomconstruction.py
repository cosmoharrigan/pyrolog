import py
from prolog.interpreter import helper, term, error
from prolog.interpreter import continuation
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# analysing and construction atoms


class AtomConcatContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, var1, var2, result):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.var1 = var1
        self.var2 = var2
        self.r = helper.convert_to_str(result)
        self.i = 0
        
    def activate(self, fcont, heap):
        # nondeterministic splitting of result        
        if self.i < len(self.r)+1:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            oldstate = heap.branch()
            self.var1.unify(term.Callable.build(self.r[:self.i]), heap)
            self.var2.unify(term.Callable.build(self.r[self.i:]), heap)
            self.i += 1
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()

@expose_builtin("atom_concat", unwrap_spec=["obj", "obj", "obj"], handles_continuation=True)
def impl_atom_concat(engine, heap, a1, a2, result, scont, fcont):
    if isinstance(a1, term.Var):
        if isinstance(a2, term.Var):
            atom_concat_cont = AtomConcatContinuation(engine, scont, fcont, heap, a1, a2, result)
            return atom_concat_cont, fcont, heap
        else:
            s2 = helper.convert_to_str(a2)
            r = helper.convert_to_str(result)
            if r.endswith(s2):
                stop = len(r) - len(s2)
                assert stop > 0
                a1.unify(term.Callable.build(r[:stop]), heap)
            else:
                raise error.UnificationFailed()
    else:
        s1 = helper.convert_to_str(a1)
        if isinstance(a2, term.Var):
            r = helper.convert_to_str(result)
            if r.startswith(s1):
                a2.unify(term.Callable.build(r[len(s1):]), heap)
            else:
                raise error.UnificationFailed()
        else:
            s2 = helper.convert_to_str(a2)
            result.unify(term.Callable.build(s1 + s2), heap)
    return scont, fcont, heap

@expose_builtin("atom_length", unwrap_spec = ["atom", "obj"])
def impl_atom_length(engine, heap, s, length):
    if not (isinstance(length, term.Var) or isinstance(length, term.Number)):
        error.throw_type_error("integer", length)
    term.Number(len(s)).unify(length, heap)

#@expose_builtin("sub_atom", unwrap_spec=["atom", "obj", "obj", "obj", "obj"],
#                handles_continuation=True)
def impl_sub_atom(engine, heap, s, before, length, after, sub, continuation):
    # XXX can possibly be optimized
    if isinstance(length, term.Var):
        startlength = 0
        stoplength = len(s) + 1
    else:
        startlength = helper.unwrap_int(length)
        stoplength = startlength + 1
        if startlength < 0:
            startlength = 0
            stoplength = len(s) + 1
    if isinstance(before, term.Var):
        startbefore = 0
        stopbefore = len(s) + 1
    else:
        startbefore = helper.unwrap_int(before)
        if startbefore < 0:
            startbefore = 0
            stopbefore = len(s) + 1
        else:
            stopbefore = startbefore + 1
    oldstate = heap.branch()
    if not isinstance(sub, term.Var):
        s1 = helper.unwrap_atom(sub)
        if len(s1) >= stoplength or len(s1) < startlength:
            raise error.UnificationFailed()
        start = startbefore
        while True:
            try:
                b = s.find(s1, start, stopbefore + len(s1)) # XXX -1?
                if b < 0:
                    break
                start = b + 1
                before.unify(term.Number(b), heap)
                after.unify(term.Number(len(s) - len(s1) - b), heap)
                length.unify(term.Number(len(s1)), heap)
                result = continuation.call(engine, choice_point=True)
                heap.discard(oldstate)
                return result
            except error.UnificationFailed:
                heap.revert(oldstate)
        raise error.UnificationFailed()
    if isinstance(after, term.Var):
        for b in range(startbefore, stopbefore):
            for l in range(startlength, stoplength):
                if l + b > len(s):
                    continue
                try:
                    before.unify(term.Number(b), heap)
                    after.unify(term.Number(len(s) - l - b), heap)
                    length.unify(term.Number(l), heap)
                    sub.unify(term.Callable.build(s[b:b + l]), heap)
                    result = continuation.call(engine, choice_point=True)
                    heap.discard(oldstate)
                    return result
                except error.UnificationFailed:
                    heap.revert(oldstate)
    else:
        a = helper.unwrap_int(after)
        for l in range(startlength, stoplength):
            b = len(s) - l - a
            assert b >= 0
            if l + b > len(s):
                continue
            try:
                before.unify(term.Number(b), heap)
                after.unify(term.Number(a), heap)
                length.unify(term.Number(l), heap)
                sub.unify(term.Callable.build(s[b:b + l]), heap)
                result = continuation.call(engine, choice_point=True)
                heap.discard(oldstate)
                return result
            except error.UnificationFailed:
                heap.revert(oldstate)
    raise error.UnificationFailed()

