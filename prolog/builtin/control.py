from prolog.interpreter import helper, term, error, continuation
from prolog.builtin.register import expose_builtin
from prolog.interpreter.signature import Signature

ifsig = Signature.getsignature("->", 2)
cutsig = Signature.getsignature("!", 0)
CUTATOM = term.Callable.build("!")

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
    
    def cut(self, heap):
        heap = self.undoheap.discard(heap)
        return self.fcont.cut(heap)
        
@expose_builtin("!", unwrap_spec=[], handles_continuation=True)
def impl_cut(engine, heap, scont, fcont):
    if fcont:
        fcont = fcont.cut(heap)
    return scont, fcont, heap

@expose_builtin(",", unwrap_spec=["callable", "raw"], handles_continuation=True)
def impl_and(engine, heap, call1, call2, scont, fcont):
    if not isinstance(call2, term.Var) and not isinstance(call2, term.Callable):
        return error.throw_type_error('callable', call2)
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

    def cut(self, heap):
        assert self.undoheap is not None
        return self.orig_fcont.cut(heap)

    def fail(self, heap):
        assert self.undoheap is not None
        heap = heap.revert_upto(self.undoheap, discard_choicepoint=True)
        self.undoheap = None
        return self, self.orig_fcont, heap

    def __repr__(self):
        return "<OrContinuation altcall=%s" % (self.altcall, )

            
@expose_builtin(";", unwrap_spec=["callable", "callable"],
                handles_continuation=True)
def impl_or(engine, heap, call1, call2, scont, fcont):
    # sucks a bit to have to special-case A -> B ; C here :-(
    if call1.signature().eq(ifsig):
        assert helper.is_term(call1)
        scont = fcont = continuation.CutDelimiter.insert_cut_delimiter(engine, scont, fcont)
        fcont = OrContinuation(engine, scont, heap, fcont, call2)
        newscont, fcont, heap = impl_if(
                engine, heap, helper.ensure_callable(call1.argument_at(0)),
                call1.argument_at(1), scont, fcont, insert_cutdelimiter=False)
        return newscont, fcont, heap.branch()
    else:
        fcont = OrContinuation(engine, scont, heap, fcont, call2)
        newscont = continuation.BodyContinuation(engine, scont, call1)
        return newscont, fcont, heap.branch()

class NotSuccessContinuation(continuation.Continuation):
    def __init__(self, engine, nextcont, heap):
        assert isinstance(nextcont, continuation.FailureContinuation)
        continuation.Continuation.__init__(self, engine, nextcont)
        self.undoheap = heap

    def activate(self, fcont, heap):
        heap.revert_upto(self.undoheap)
        if self.nextcont is None:
            raise error.UnificationFailed
        nextcont = self.nextcont
        assert isinstance(nextcont, continuation.FailureContinuation)
        return nextcont.fail(self.undoheap)

class NotFailureContinuation(continuation.FailureContinuation):
    def __init__(self, engine, nextcont, orig_fcont, heap):
        continuation.FailureContinuation.__init__(self, engine, nextcont)
        self.undoheap = heap
        self.orig_fcont = orig_fcont

    def activate(self, fcont, heap):
        assert 0, "Unreachable"

    def fail(self, heap):
        heap.revert_upto(self.undoheap)
        return self.nextcont, self.orig_fcont, self.undoheap


@expose_builtin(["not", "\\+"], unwrap_spec=["callable"],
                handles_continuation=True)
def impl_not(engine, heap, call, scont, fcont):
    notscont = NotSuccessContinuation(engine, fcont, heap)
    notfcont = NotFailureContinuation(engine, scont, fcont, heap)
    newscont = continuation.BodyContinuation(engine, notscont, call)
    return newscont, notfcont, heap.branch()


@expose_builtin("->", unwrap_spec=["callable", "raw"],
                handles_continuation=True)
def impl_if(engine, heap, if_clause, then_clause, scont, fcont,
            insert_cutdelimiter=True):
    scont = continuation.BodyContinuation(engine, scont, then_clause)
    if insert_cutdelimiter:
        scont = fcont = continuation.CutDelimiter.insert_cut_delimiter(engine, scont, fcont)
    body = term.Callable.build(",", [if_clause, CUTATOM])
    return continuation.BodyContinuation(engine, scont, body), fcont, heap
