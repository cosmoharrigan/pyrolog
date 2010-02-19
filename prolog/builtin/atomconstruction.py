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



class SubAtomContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, atom, before, length, after, sub):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.atom = atom
        self.before = before
        self.length = length
        self.after = after
        self.sub = sub
        self.setup()
    
    def setup(self):
        if isinstance(self.length, term.Var):
            self.startlength = 0
            self.stoplength = len(self.atom) + 1
        else:
            self.startlength = helper.unwrap_int(self.length)
            self.stoplength = self.startlength + 1
            if self.startlength < 0:
                self.startlength = 0
                self.stoplength = len(self.atom) + 1
        if isinstance(self.before, term.Var):
            self.startbefore = 0
            self.stopbefore = len(self.atom) + 1
        else:
            self.startbefore = helper.unwrap_int(self.before)
            if self.startbefore < 0:
                self.startbefore = 0
                self.stopbefore = len(self.atom) + 1
            else:
                self.stopbefore = self.startbefore + 1


class SubAtomNonVarSubContinuation(SubAtomContinuation):
    def __init__(self, engine, scont, fcont, heap, atom, before, length, after, sub):
        SubAtomContinuation.__init__(self, engine, scont, fcont, heap,
                                            atom, before, length, after, sub)
        self.s1 = helper.unwrap_atom(sub)
        if len(self.s1) >= self.stoplength or len(self.s1) < self.startlength:
            raise error.UnificationFailed()
        self.start = self.startbefore
    def activate(self, fcont, heap):
        b = self.atom.find(self.s1, self.start, self.stopbefore + len(self.s1)) # XXX -1?
        if b < 0:
            raise error.UnificationFailed()
        fcont, heap = self.prepare_more_solutions(fcont, heap)
        self.start = b + 1
        try:
            self.before.unify(term.Number(b), heap)
            self.after.unify(term.Number(len(self.atom) - len(self.s1) - b), heap)
            self.length.unify(term.Number(len(self.s1)), heap)
        except error.UnificationFailed:
            pass
        return self.nextcont, fcont, heap
    
    def __repr__(self):
        return "<SubAtomNonVarSubContinuation(%r)>" % self.__dict__

class SubAtomVarAfterContinuation(SubAtomContinuation):
    def __init__(self, engine, scont, fcont, heap, atom,
                                                before, length, after, sub):
        SubAtomContinuation.__init__(self, engine, scont, fcont, heap, atom,
                                                    before, length, after, sub)
        self.b = self.startbefore
        self.l = self.startlength
        print 'foo'
    def activate(self, fcont, heap):
        if self.b < self.stopbefore:
            if self.l < self.stoplength:
                if self.l + self.b > len(self.atom):
                    self.b += 1
                    self.l = self.startlength
                    return self.activate(fcont, heap)
                fcont, heap = self.prepare_more_solutions(fcont, heap)
                
                self.before.unify(term.Number(self.b), heap)
                self.after.unify(term.Number(
                                    len(self.atom) - self.l - self.b), heap)
                self.length.unify(term.Number(self.l), heap)
                self.sub.unify(term.Callable.build(
                                    self.atom[self.b:self.b + self.l]), heap)
                self.l += 1
                return self.nextcont, fcont, heap
            else:
                self.b += 1
                self.l = self.startlength
                return self.activate(fcont, heap)
        raise error.UnificationFailed()

class SubAtomElseContinuation(SubAtomContinuation):
    def __init__(self, engine, scont, fcont, heap, atom,
                                                before, length, after, sub):
        SubAtomContinuation.__init__(self, engine, scont, fcont, heap, atom,
                                                    before, length, after, sub)
        self.a = helper.unwrap_int(after)
        self.l = self.startlength
    def activate(self, fcont, heap):
        if self.l < self.stoplength:
            b = len(self.atom) - self.l - self.a
            assert b >= 0
            if self.l + b > len(self.atom):
                self.l += 1
                return self.activate(fcont, heap)
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.before.unify(term.Number(b), heap)
            self.after.unify(term.Number(self.a), heap)
            self.length.unify(term.Number(self.l), heap)
            self.sub.unify(term.Callable.build(self.atom[b:b + self.l]), heap)
            self.l += 1
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()

@expose_builtin("sub_atom", unwrap_spec=["atom", "obj", "obj", "obj", "obj"],
                                                    handles_continuation=True)
def impl_sub_atom(engine, heap, s, before, length, after, sub, scont, fcont):
    if not isinstance(sub, term.Var):
        cls = SubAtomNonVarSubContinuation
    elif isinstance(after, term.Var):
        cls = SubAtomVarAfterContinuation
    else:
        cls = SubAtomElseContinuation
    cont =  cls(engine, scont, fcont, heap, s, before, length, after, sub)
    return cont, fcont, heap

