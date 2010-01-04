import py
from prolog.interpreter import continuation, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# meta-call predicates

@expose_builtin("call", unwrap_spec=["callable"],
                handles_continuation=True)
def impl_call(engine, heap, call, scont, fcont):
    scont = fcont = continuation.CutDelimiter(engine, scont, fcont)
    return engine.call(call, scont, fcont, heap)

#@expose_builtin("once", unwrap_spec=["callable"],
#                handles_continuation=True)
def impl_once(engine, heap, clause, continuation):
    engine.call(clause)
    return continuation.call(engine, choice_point=False)

