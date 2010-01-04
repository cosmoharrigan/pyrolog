import py
from prolog.interpreter import continuation, helper, term, error
from prolog.builtin.register import expose_builtin
from prolog.builtin.type import impl_ground

# ___________________________________________________________________
# exception handling

@expose_builtin("catch", unwrap_spec=["callable", "obj", "callable"],
                handles_continuation=True)
def impl_catch(engine, heap, goal, catcher, recover, scont, fcont):
    new_heap = heap.branch()
    scont = continuation.CatchingDelimiter(engine, scont, fcont, catcher, recover, heap)
    return engine.call(goal, scont, fcont, heap)
    try:
        heap.discard(old_state)
        return result
    except error.CatchableError, e:
        if not catching_continuation.scope_active:
            raise
        exc_term = e.term.getvalue(heap)
        heap.revert_and_discard(old_state)
        d = {}
        exc_term = exc_term.copy(heap, d)
        try:
            impl_ground(engine, heap, exc_term)
        except error.UnificationFailed:
            raise error.UncatchableError(
                "not implemented: catching of non-ground terms")
        try:
            catcher.unify(exc_term, heap)
        except error.UnificationFailed:
            if isinstance(e, error.UserError):
                raise error.UserError(exc_term)
            if isinstance(e, error.CatchableError):
                raise error.CatchableError(exc_term)
        return engine.call(recover, continuation, choice_point=False)

@expose_builtin("throw", unwrap_spec=["obj"], handles_continuation=True)
def impl_throw(engine, heap, exc, scont, fcont):
    return engine.throw(exc, scont, fcont, heap)

