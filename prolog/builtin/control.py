import py
from prolog.interpreter import engine, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# control predicates

@expose_builtin("fail", unwrap_spec=[])
def impl_fail(engine, heap):
    raise error.UnificationFailed()

@expose_builtin("true", unwrap_spec=[])
def impl_true(engine, heap):
    return

@expose_builtin("repeat", unwrap_spec=[], handles_continuation=True)
def impl_repeat(engine, heap, continuation):
    while 1:
        try:
            return continuation.call(engine, choice_point=True)
        except error.UnificationFailed:
            pass

@expose_builtin("!", unwrap_spec=[], handles_continuation=True)
def impl_cut(engine, heap, continuation):
    raise error.CutException(continuation)

class AndContinuation(engine.Continuation):
    def __init__(self, next_call, continuation):
        self.next_call = next_call
        self.continuation = continuation

    def _call(self, engine):
        next_call = self.next_call.dereference(engine.heap)
        next_call = helper.ensure_callable(next_call)
        return engine.call(next_call, self.continuation, choice_point=False)

@expose_builtin(",", unwrap_spec=["callable", "raw"], handles_continuation=True)
def impl_and(engine, heap, call1, call2, continuation):
    if not isinstance(call2, term.Var) and not isinstance(call2, term.Callable):
        error.throw_type_error('callable', call2)
    and_continuation = AndContinuation(call2, continuation)
    return engine.call(call1, and_continuation, choice_point=False)

@expose_builtin(";", unwrap_spec=["callable", "callable"],
                handles_continuation=True)
def impl_or(engine, heap, call1, call2, continuation):
    oldstate = heap.branch()
    try:
        return engine.call(call1, continuation, choice_point=True)
    except error.UnificationFailed:
        heap.revert_and_discard(oldstate)
    return engine.call(call2, continuation, choice_point=False)

@expose_builtin(["not", "\\+"], unwrap_spec=["callable"])
def impl_not(engine, heap, call):
    try:
        try:
            engine.call(call)
        except error.CutException, e:
            engine.continue_after_cut(e.continuation)
    except error.UnificationFailed:
        return None
    raise error.UnificationFailed()

@expose_builtin("->", unwrap_spec=["callable", "raw"],
                handles_continuation=True)
def impl_if(engine, heap, if_clause, then_clause, continuation):
    oldstate = heap.branch()
    try:
        engine.call(if_clause)
    except error.UnificationFailed:
        heap.revert_and_discard(oldstate)
        raise
    return engine.call(helper.ensure_callable(then_clause), continuation,
                       choice_point=False)

