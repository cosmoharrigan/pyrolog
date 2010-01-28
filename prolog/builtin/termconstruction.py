import py
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# analysing and construction terms

@expose_builtin("functor", unwrap_spec=["obj", "obj", "obj"])
def impl_functor(engine, heap, t, functor, arity):
    if helper.is_atomic(t):
        functor.unify(t, heap)
        arity.unify(term.Number(0), heap)
    elif isinstance(t, term.Term):
        functor.unify(term.Atom(t.name()), heap)
        arity.unify(term.Number(t.argument_count()), heap)
    elif isinstance(t, term.Var):
        if isinstance(functor, term.Var):
            error.throw_instantiation_error()
        a = helper.unwrap_int(arity)
        if a < 0:
            error.throw_domain_error("not_less_than_zero", arity)
        else:
            functor = helper.ensure_atomic(functor)
            if a == 0:
                t.unify(helper.ensure_atomic(functor), heap)
            else:
                name = helper.unwrap_atom(functor)
                t.unify(
                    term.Callable.build(name, [term.Var() for i in range(a)]),
                    heap)

#@expose_builtin("arg", unwrap_spec=["obj", "obj", "obj"],
#handles_continuation=True)
def impl_arg(engine, heap, first, second, third, continuation):
    if isinstance(second, term.Var):
        error.throw_instantiation_error()
    if isinstance(second, term.Atom):
        raise error.UnificationFailed()
    if not isinstance(second, term.Term):
        error.throw_type_error("compound", second)
    if isinstance(first, term.Var):
        oldstate = heap.branch()
        for i in range(second.argument_count()):
            arg = second.argument_at(i)
            try:
                third.unify(arg, heap)
                first.unify(term.Number(i + 1), heap)
                result = continuation.call(engine, choice_point=True)
                heap.discard(oldstate)
                return result
            except error.UnificationFailed:
                heap.revert(oldstate)
        heap.discard(oldstate)
        raise error.UnificationFailed()
    elif isinstance(first, term.Number):
        num = first.num
        if num == 0:
            raise error.UnificationFailed
        if num < 0:
            error.throw_domain_error("not_less_than_zero", first)
        if num > second.argument_count():
            raise error.UnificationFailed()
        arg = second.argument_at(num - 1)
        third.unify(arg, heap)
    else:
        error.throw_type_error("integer", first)
    return continuation.call(engine, choice_point=False)

@expose_builtin("=..", unwrap_spec=["obj", "obj"])
def impl_univ(engine, heap, first, second):
    if not isinstance(first, term.Var):
        if isinstance(first, term.Term):
            l = [term.Atom(first.name())] + first.arguments()
        else:
            l = [first]
        u1 = helper.wrap_list(l)
        if not isinstance(second, term.Var):
            u1.unify(second, heap)
        else:
            u1.unify(second, heap)
    else:
        if isinstance(second, term.Var):
            error.throw_instantiation_error()
        else:
            l = helper.unwrap_list(second)
            head = l[0]
            if not isinstance(head, term.Atom):
                error.throw_type_error("atom", head)
            term.Callable.build(head.name(), l[1:]).unify(first, heap)

@expose_builtin("copy_term", unwrap_spec=["obj", "obj"])
def impl_copy_term(engine, heap, interm, outterm):
    d = {}
    copy = interm.copy(heap, d)
    outterm.unify(copy, heap)


