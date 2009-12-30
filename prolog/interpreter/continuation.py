from pypy.rlib import jit
from prolog.interpreter import error
from prolog.interpreter.term import Term, Atom, Rule, Var
from prolog.interpreter.function import Function

def driver(scont, fcont, heap):
    while scont is not None:
        try:
            scont, fcont, heap  = scont.activate(fcont, heap)
        except error.UnificationFailed:
            if fcont is None:
                raise
            scont, fcont, heap = fcont.fail(heap)
            if scont is None:
                raise

class Engine(object):
    def __init__(self):
        self.heap = Heap()
        self.signature2function = {}
        self.parser = None
        self.operations = None

    # _____________________________________________________
    # database functionality

    def add_rule(self, rule, end=True):
        from prolog import builtin
        if isinstance(rule, Term):
            if rule.name == ":-":
                rule = Rule(rule.args[0], rule.args[1])
            else:
                rule = Rule(rule, None)
        elif isinstance(rule, Atom):
            rule = Rule(rule, None)
        else:
            error.throw_type_error("callable", rule)
            assert 0, "unreachable" # make annotator happy
        signature = rule.signature
        if signature in builtin.builtins:
            error.throw_permission_error(
                "modify", "static_procedure", rule.head.get_prolog_signature())
        function = self._lookup(signature)
        function.add_rule(rule, end)

    @jit.purefunction_promote
    def get_builtin(self, signature):
        from prolog.builtin import builtins
        builtin = builtins.get(signature, None)
        return builtin

    @jit.purefunction
    def _lookup(self, signature):
        signature2function = self.signature2function
        function = signature2function.get(signature, None)
        if function is None:
            signature2function[signature] = function = Function()
        return function

    # _____________________________________________________
    # parsing-related functionality

    def _build_and_run(self, tree):
        from prolog.interpreter.parsing import TermBuilder
        builder = TermBuilder()
        term = builder.build_query(tree)
        if isinstance(term, Term) and term.signature == ":-/1":
            self.run(term.args[0])
        else:
            self.add_rule(term)
        return self.parser

    def runstring(self, s):
        from prolog.interpreter.parsing import parse_file
        trees = parse_file(s, self.parser, Engine._build_and_run, self)

    def parse(self, s):
        from prolog.interpreter.parsing import parse_file, TermBuilder
        builder = TermBuilder()
        trees = parse_file(s, self.parser)
        terms = builder.build_many(trees)
        return terms, builder.varname_to_var

    def getoperations(self):
        from prolog.interpreter.parsing import default_operations
        if self.operations is None:
            return default_operations
        return self.operations

    # _____________________________________________________
    # Prolog execution

    def run_query(self, query, continuation=None):
        driver(*self.call(query, continuation, None, Heap()))
    run = run_query

    def call(self, query, scont, fcont, heap):
        signature = query.signature
        builtin = self.get_builtin(signature)
        if builtin is not None:
            return builtin.call(self, query, scont, fcont, heap)

        # do a real call
        function = self._lookup(signature)
        startrulechain = function.rulechain
        if startrulechain is None:
            error.throw_existence_error(
                "procedure", query.get_prolog_signature())
        rulechain = startrulechain.find_applicable_rule(query)
        scont = UserCallContinuation(self, scont, query,
                                     rulechain)
        return scont, fcont, heap

# ___________________________________________________________________
# Heap implementation

class Heap(object):
    def __init__(self, prev=None):
        self.trail = []
        self.prev = prev

    # _____________________________________________________
    # interface that term.py uses

    def add_trail(self, var):
        """ Remember the current state of a variable to be able to backtrack it
        to that state. Usually called just before a variable changes. """
        self.trail.append((var, var.binding))

    def newvar(self):
        """ Make a new variable. Should return a Var instance, possibly with
        interesting attributes set that e.g. add_trail can inspect."""
        result = Var()
        return result

    # _____________________________________________________

    def branch(self):
        """ Branch of a heap for a choice point. The return value is the new
        heap that should be used from now on, self is the heap that can be
        backtracked to."""
        res = Heap(self)
        return res

    def revert_upto(self, heap):
        """ Revert to the heap corresponding to a choice point. The return
        value is the new heap that should be used."""
        previous = None
        while self is not heap:
            self._revert()
            previous = self
            self = self.prev
        return previous

    def _revert(self):
        for var, oldbinding in self.trail:
            var.binding = oldbinding
        self.trail = []

# ___________________________________________________________________
# Continuation classes

class Continuation(object):
    """ Represents a continuation of the Prolog computation. This can be seen
    as an RPython-compatible way to express closures. """

    def __init__(self, engine, nextcont):
        self.engine = engine
        self.nextcont = nextcont

    def activate(self, fcont, heap):
        """ Follow the continuation. heap is the heap that should be used while
        doing so, fcont the failure continuation that should be activated in
        case this continuation fails. This method can only be called once, i.e.
        it can destruct this object. 
        
        The method should return a triple (next cont, failure cont, heap)"""
        raise NotImplementedError("abstract base class")

class FailureContinuation(Continuation):
    """ A continuation that can represent failures. It has a .fail method that
    is called to prepare it for being used as a failure continuation.
    
    NB: a Continuation can be used both as a failure continuation and as a
    success continuation."""

    def fail(self, heap):
        """ Needs to be called to prepare the object as being used as a failure
        continuation. Particularly useful for objects that are both a regular
        and a failure continuation. """
        # returns (next cont, failure cont, heap)
        raise NotImplementedError("abstract base class")

class BodyContinuation(Continuation):
    """ Represents a bit of Prolog code that is still to be called. """
    def __init__(self, engine, nextcont, body):
        Continuation.__init__(self, engine, nextcont)
        self.body = body

    def activate(self, fcont, heap):
        return self.engine.call(self.body, self.nextcont, fcont, heap)

    def __repr__(self):
        return "<BodyContinuation %r>" % (self.body, )

class ChoiceContinuation(FailureContinuation):
    """ An abstract base class for Continuations that represent a choice point,
    i.e. a point to which the execution can backtrack to."""

    def __init__(self, *args):
        FailureContinuation.__init__(self, *args)
        self.undoheap = None
        self.orig_fcont = None

    #def activate(self, fcont, heap):
    #    this method needs to be structured as follows:
    #    <some code>
    #    if <has more solutions>:
    #        fcont, heap = self.prepare_more_solutions(fcont, heap)
    #    <construct cont> # must not raise UnificationFailed!
    #    return cont, fcont, heap

    def prepare_more_solutions(self, fcont, heap):
        self.undoheap = heap
        heap = heap.branch()
        self.orig_fcont = fcont
        fcont = self
        return fcont, heap
    
    def fail(self, heap):
        assert self.undoheap is not None
        heap = heap.revert_upto(self.undoheap)
        return self, self.orig_fcont, heap

class UserCallContinuation(ChoiceContinuation):
    def __init__(self, engine, nextcont, query, rulechain):
        ChoiceContinuation.__init__(self, engine, nextcont)
        self.query = query
        signature = query.signature
        self.rulechain = rulechain

    def activate(self, fcont, heap):
        rulechain = self.rulechain
        query = self.query
        restchain = rulechain.find_next_applicable_rule(query)
        if restchain is not None:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.rulechain = restchain
        cont = RuleContinuation(self.engine, self.nextcont, rulechain.rule, query)
        return cont, fcont, heap

    def __repr__(self):
        return "<UserCallContinuation query=%r rule=%r>" % (
                self.query, self.rulechain.rule, )

class RuleContinuation(Continuation):
    def __init__(self, engine, nextcont, rule, query):
        Continuation.__init__(self, engine, nextcont)
        self.rule = rule
        self.query = query

    def activate(self, fcont, heap):
        nextcall = self.rule.clone_and_unify_head(heap, self.query)
        if nextcall is not None:
            cont = BodyContinuation(self.engine, self.nextcont, nextcall)
        else:
            cont = self.nextcont
        return cont, fcont, heap
