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
    return continuation.BodyContinuation(engine, scont, goal), fcont, heap

@expose_builtin("throw", unwrap_spec=["obj"], handles_continuation=True)
def impl_throw(engine, heap, exc, scont, fcont):
    return engine.throw(exc, scont, fcont, heap)

