import py
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.continuation import Continuation, Heap, Engine
from prolog.interpreter.parsing import parse_file, TermBuilder
def assert_true(query, e=None):
    if e is None:
        e = Engine()
    terms, vars = e.parse(query)
    term, = terms
    e.run(term)
    return dict([(name, var.dereference(e.heap))
                     for name, var in vars.iteritems()])
def assert_false(query, e=None):
    if e is None:
        e = Engine()
    term = e.parse(query)[0][0]
    py.test.raises(UnificationFailed, e.run, term)

def prolog_raises(exc, query, e=None):
    return assert_true("catch(((%s), fail), error(%s), true)." %
                       (query, exc), e)

class CollectAllContinuation(Continuation):
    nextcont = None
    def __init__(self, vars):
        self.heaps = []
        self.vars = vars
        self._candiscard = True

    def activate(self, fcont, heap):
        self.heaps.append(dict([(name, var.dereference(heap))
                                    for name, var in self.vars.iteritems()]))
        print "restarting computation"
        raise UnificationFailed

def collect_all(engine, s):
    terms, vars = engine.parse(s)
    term, = terms
    collector = CollectAllContinuation(vars)
    py.test.raises(UnificationFailed, engine.run, term,
                   collector)
    return collector.heaps

def parse(inp):
    t = parse_file(inp)
    builder = TermBuilder()
    return builder.build(t)

