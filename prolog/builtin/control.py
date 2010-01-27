from prolog.interpreter import helper, term, error, continuation
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
    # sucks a bit to have to special-case A -> B ; C here :-(
    if call1.signature == "->/2":
        assert isinstance(call1, term.Term)
        scont = fcont = continuation.CutDelimiter(engine, scont, fcont)
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
        continuation.Continuation.__init__(self, engine, nextcont)
        self.undoheap = heap

    def activate(self, fcont, heap):
        heap.revert_upto(self.undoheap)
        if self.nextcont is None:
            raise error.UnificationFailed
        return self.nextcont.fail(self.undoheap)

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

CUTATOM = term.Atom.newatom("!")

@expose_builtin("->", unwrap_spec=["callable", "raw"],
                handles_continuation=True)
def impl_if(engine, heap, if_clause, then_clause, scont, fcont,
            insert_cutdelimiter=True):
    scont = continuation.BodyContinuation(engine, scont, then_clause)
    if insert_cutdelimiter:
        scont = fcont = continuation.CutDelimiter(engine, scont, fcont)
    body = term.Term(",", [if_clause, CUTATOM])
    return continuation.BodyContinuation(engine, scont, body), fcont, heap
