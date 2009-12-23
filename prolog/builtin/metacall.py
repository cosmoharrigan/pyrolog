import py
from prolog.interpreter import engine, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# meta-call predicates

@expose_builtin("call", unwrap_spec=["callable"],
                handles_continuation=True)
def impl_call(engine, heap, call, continuation):
    try:
        return engine.call(call, continuation)
    except error.CutException, e:
        return e.continuation.call(engine, choice_point=False)

@expose_builtin("once", unwrap_spec=["callable"],
                handles_continuation=True)
def impl_once(engine, heap, clause, continuation):
    engine.call(clause)
    return continuation.call(engine, choice_point=False)

