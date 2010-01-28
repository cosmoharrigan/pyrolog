import py
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# finding all solutions to a goal

class FindallContinuation(engine.Continuation):
    def __init__(self, template):
        self.found = []
        self.template = template

    def _call(self, engine):
        clone = self.template.getvalue(engine.heap)
        self.found.append(clone)
        raise error.UnificationFailed()

@expose_builtin("findall", unwrap_spec=['raw', 'callable', 'raw'])
def impl_findall(engine, heap, template, goal, bag):
    oldstate = heap.branch()
    collector = FindallContinuation(template)
    try:
        engine.call(goal, collector)
    except error.UnificationFailed:
        heap.revert_and_discard(oldstate)
    else:
        assert 0, "unreachable"
    result = term.Atom.newatom("[]")
    for i in range(len(collector.found) - 1, -1, -1):
        copy = collector.found[i]
        d = {}
        copy = copy.copy(heap, d)
        result = term.Callable.build(".", [copy, result])
    bag.unify(result, heap)
