import py
from prolog.interpreter import engine, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# analysing and construction atoms

#@expose_builtin("atom_concat", unwrap_spec=["obj", "obj", "obj"],
#                handles_continuation=True)
def impl_atom_concat(engine, heap, a1, a2, result, continuation):
    if isinstance(a1, term.Var):
        if isinstance(a2, term.Var):
            # nondeterministic splitting of result
            r = helper.convert_to_str(result)
            for i in range(len(r) + 1):
                oldstate = heap.branch()
                try:
                    a1.unify(term.Atom(r[:i]), heap)
                    a2.unify(term.Atom(r[i:]), heap)
                    result = continuation.call(engine, choice_point=True)
                    heap.discard(oldstate)
                    return result
                except error.UnificationFailed:
                    heap.revert(oldstate)
            raise error.UnificationFailed()
        else:
            s2 = helper.convert_to_str(a2)
            r = helper.convert_to_str(result)
            if r.endswith(s2):
                stop = len(r) - len(s2)
                assert stop > 0
                a1.unify(term.Atom(r[:stop]), heap)
            else:
                raise error.UnificationFailed()
    else:
        s1 = helper.convert_to_str(a1)
        if isinstance(a2, term.Var):
            r = helper.convert_to_str(result)
            if r.startswith(s1):
                a2.unify(term.Atom(r[len(s1):]), heap)
            else:
                raise error.UnificationFailed()
        else:
            s2 = helper.convert_to_str(a2)
            result.unify(term.Atom(s1 + s2), heap)
    return continuation.call(engine, choice_point=False)

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
                    sub.unify(term.Atom(s[b:b + l]), heap)
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
                sub.unify(term.Atom(s[b:b + l]), heap)
                result = continuation.call(engine, choice_point=True)
                heap.discard(oldstate)
                return result
            except error.UnificationFailed:
                heap.revert(oldstate)
    raise error.UnificationFailed()

