import py
from prolog.interpreter import helper, term, error, continuation
from prolog.builtin.register import expose_builtin
# ___________________________________________________________________
# analysing and construction terms

@expose_builtin("functor", unwrap_spec=["obj", "obj", "obj"])
def impl_functor(engine, heap, t, functor, arity):
    if helper.is_atomic(t):
        functor.unify(t, heap)
        arity.unify(term.Number(0), heap)
    elif helper.is_term(t):
        functor.unify(term.Callable.build(t.name()), heap)
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

class ArgContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, first, second, third):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.first = first
        self.second = second
        self.third = third
        self.i = 0
        
    def activate(self, fcont, heap):
        if self.i < self.second.argument_count():
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            oldstate = heap.branch()
            arg = self.second.argument_at(self.i)
            # try:
            self.third.unify(arg, heap)
            self.first.unify(term.Number(self.i + 1), heap)
            self.i += 1
            return self.nextcont, fcont, heap
            # except error.UnificationFailed:
                # oldstate.revert_upto(heap)
        raise error.UnificationFailed()
        
@expose_builtin("arg", unwrap_spec=["obj", "obj", "obj"],
handles_continuation=True)
def impl_arg(engine, heap, first, second, third, scont, fcont):
    if isinstance(second, term.Var):
        error.throw_instantiation_error()
    if helper.is_atomic(second):
        raise error.UnificationFailed()
    if not helper.is_term(second):
        error.throw_type_error("compound", second)
    if isinstance(first, term.Var):
        a = ArgContinuation(engine, scont, fcont, heap, first, second, third)
        return a, fcont, heap
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
    return scont, fcont, heap

@expose_builtin("=..", unwrap_spec=["obj", "obj"])
def impl_univ(engine, heap, first, second):
    if not isinstance(first, term.Var):
        if not isinstance(first, term.Atom):
            l = [term.Callable.build(first.name())] + first.arguments()
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


