import py
from prolog.interpreter import helper, term, error, continuation, memo
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# finding all solutions to a goal

class FindallContinuation(continuation.Continuation):
    def __init__(self, engine, template, heap):
        continuation.Continuation.__init__(self, engine, None)
        self.resultvar = self.fullsolution = heap.newvar()
        self.template = template
        self.heap = heap

    def activate(self, fcont, _):
        m = memo.CopyMemo()
        clone = self.template.copy(self.heap, m)
        newresultvar = self.heap.newvar()
        result = term.Callable.build(".", [clone, newresultvar])
        self.resultvar.setvalue(result, self.heap)
        self.resultvar = newresultvar
        raise error.UnificationFailed()

class DoneWithFindallContinuation(continuation.FailureContinuation):
    def __init__(self, engine, heap, collector, scont, fcont, bag):
        continuation.Continuation.__init__(self, engine, scont)
        self.collector = collector
        self.orig_fcont = fcont
        self.undoheap = heap
        self.bag = bag

    def activate(self, fcont, heap):
        raise NotImplementedError

    def fail(self, heap):
        heap = heap.revert_upto(self.undoheap)
        result = term.Callable.build("[]")
        resultvar = self.collector.resultvar
        resultvar.setvalue(result, heap)
        self.bag.unify(self.collector.fullsolution, heap)
        return self.nextcont, self.orig_fcont, heap



@expose_builtin("findall", unwrap_spec=['raw', 'callable', 'raw'],
                handles_continuation=True)
def impl_findall(engine, heap, template, goal, bag, scont, fcont):
    newheap = heap.branch()
    collector = FindallContinuation(engine, template, heap)
    newscont = continuation.BodyContinuation(engine, scont.module, collector, goal)
    fcont = DoneWithFindallContinuation(engine, heap, collector, scont, fcont, bag)
    return newscont, fcont, newheap
