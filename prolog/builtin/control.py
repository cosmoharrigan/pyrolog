from prolog.interpreter import engine, helper, term, error, continuation
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
def impl_repeat(engine, heap, scont, fcont):
    return scont, RepeatContinuation(engine, scont, fcont, heap), heap.branch()

class RepeatContinuation(continuation.FailureContinuation):
    def __init__(self, engine, scont, fcont, heap):
        continuation.FailureContinuation.__init__(self, engine, scont)
        self.fcont = fcont
        self.undoheap = heap
        
    def activate(self, fcont, heap):
        assert 0, "Unreachable"
        
    def fail(self, heap):
        heap = heap.revert_upto(self.undoheap)
        return self.nextcont, self, heap
    
    def cut(self):
        if self.fcont is not None:
            return self.fcont.cut()
        return None
        
@expose_builtin("!", unwrap_spec=[], handles_continuation=True)
def impl_cut(engine, heap, scont, fcont):
    if fcont:
        fcont = fcont.cut()
    return scont, fcont, heap

@expose_builtin(",", unwrap_spec=["callable", "raw"], handles_continuation=True)
def impl_and(engine, heap, call1, call2, scont, fcont):
    if not isinstance(call2, term.Var) and not isinstance(call2, term.Callable):
        return engine.throw_type_error('callable', call2, scont, fcont, heap)
    scont = continuation.BodyContinuation(engine, scont, call2)
    return engine.call(call1, scont, fcont, heap)

class OrContinuation(continuation.FailureContinuation):
    def __init__(self, engine, nextcont, undoheap, orig_fcont, altcall):
        continuation.FailureContinuation.__init__(self, engine, nextcont)
        self.altcall = altcall
        self.undoheap = undoheap
        self.orig_fcont = orig_fcont

    def activate(self, fcont, heap):
        assert self.undoheap is None
        scont = continuation.BodyContinuation(self.engine, self.nextcont,
                                              self.altcall)
        return scont, fcont, heap

    def cut(self):
        assert self.undoheap is not None
        return self.orig_fcont.cut()

    def fail(self, heap):
        assert self.undoheap is not None
        heap = heap.revert_upto(self.undoheap)
        self.undoheap = None
        return self, self.orig_fcont, heap

    def __repr__(self):
        return "<OrContinuation altcall=%s" % (self.altcall, )

            
@expose_builtin(";", unwrap_spec=["callable", "callable"],
                handles_continuation=True)
def impl_or(engine, heap, call1, call2, scont, fcont):
    newscont = continuation.BodyContinuation(engine, scont, call1)
    fcont = OrContinuation(engine, scont, heap, fcont, call2)
    return newscont, fcont, heap.branch()

#@expose_builtin(["not", "\\+"], unwrap_spec=["callable"],
#                handles_continuation=True)
def impl_not(engine, heap, call, scont, fcont):
    newscont = continuation.BodyContinuation(engine, XXX(scont), call1)
    try:
        try:
            engine.call(call)
        except error.CutException, e:
            engine.continue_after_cut(e.continuation)
    except error.UnificationFailed:
        return None
    raise error.UnificationFailed()

#@expose_builtin("->", unwrap_spec=["callable", "raw"],
#                handles_continuation=True)
def impl_if(engine, heap, if_clause, then_clause, continuation):
    oldstate = heap.branch()
    try:
        engine.call(if_clause)
    except error.UnificationFailed:
        heap.revert_and_discard(oldstate)
        raise
    return engine.call(helper.ensure_callable(then_clause), continuation,
                       choice_point=False)

