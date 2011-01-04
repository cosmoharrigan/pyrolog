import py
from prolog.interpreter import helper, term, error, continuation
from prolog.builtin.register import expose_builtin
from pypy.rlib import jit
# ___________________________________________________________________
# analysing and construction terms

@expose_builtin("functor", unwrap_spec=["obj", "obj", "obj"])
def impl_functor(engine, heap, t, functor, arity):
    if helper.is_atomic(t):
        functor.unify(t, heap)
        arity.unify(term.Number(0), heap)
    elif helper.is_term(t):
        assert isinstance(t, term.Callable)
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
            arg = self.second.argument_at(self.i)
            self.i += 1
            try:
                self.third.unify(arg, heap)
                self.first.unify(term.Number(self.i), heap)
            except error.UnificationFailed, e:
                return fcont, self.orig_fcont, heap
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()

@expose_builtin("arg", unwrap_spec=["obj", "obj", "obj"],
handles_continuation=True)
def impl_arg(engine, heap, first, second, third, scont, fcont):
    if isinstance(second, term.Var):
        error.throw_instantiation_error()
    if helper.is_atomic(second):
    #    raise error.UnificationFailed()
        error.throw_type_error('compound', second)
    if not helper.is_term(second):
        error.throw_type_error("compound", second)
    assert isinstance(second, term.Callable)
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
@jit.unroll_safe
def impl_univ(engine, heap, first, second):
    if not isinstance(first, term.Var):
        if helper.is_term(first):
            assert isinstance(first, term.Callable)
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
            l2 = [None] * (len(l) - 1)
            for i in range(len(l2)):
                l2[i] = l[i + 1]
            name = jit.hint(head.signature(), promote=True).name
            term.Callable.build(name, l2).unify(first, heap)

@expose_builtin("copy_term", unwrap_spec=["obj", "obj"])
def impl_copy_term(engine, heap, interm, outterm):
    from prolog.interpreter.memo import CopyMemo
    m = CopyMemo()
    copy = interm.copy(heap, m)
    outterm.unify(copy, heap)


