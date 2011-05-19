import py
import time
from pypy.rlib import jit
from pypy.rlib.objectmodel import we_are_translated, specialize
from prolog.interpreter import error
from prolog.interpreter import helper
from prolog.interpreter.term import Term, Atom, Var, Callable
from prolog.interpreter.function import Function, Rule
from prolog.interpreter.heap import Heap
from prolog.interpreter.signature import Signature

Signature.register_extr_attr("function", engine=True)

# ___________________________________________________________________
# JIT stuff

def get_printable_location(rule):
    if rule:
        s = rule.signature.string()
    else:
        s = "No rule"
    return s

def get_jitcell_at(where, rule):
    # XXX can be vastly simplified
    return rule.jit_cells.get(where, None)

def set_jitcell_at(newcell, where, rule):
    # XXX can be vastly simplified
    rule.jit_cells[where] = newcell

predsig = Signature.getsignature(":-", 2)
callsig = Signature.getsignature(":-", 1)

jitdriver = jit.JitDriver(
        greens=["rule"],
        reds=["scont", "fcont", "heap"],
        get_printable_location=get_printable_location,
        #get_jitcell_at=get_jitcell_at,
        #set_jitcell_at=set_jitcell_at,
        )

# ___________________________________________________________________
# end JIT stuff


def driver(scont, fcont, heap):
    rule = None
    while not scont.is_done():
        #view(scont, fcont, heap)
        if isinstance(scont, RuleContinuation) and scont._rule.body is not None:
            rule = scont._rule
            jitdriver.can_enter_jit(rule=rule, scont=scont, fcont=fcont,
                                    heap=heap)
        try:
            jitdriver.jit_merge_point(rule=rule, scont=scont, fcont=fcont,
                                      heap=heap)
            scont, fcont, heap  = scont.activate(fcont, heap)
        except error.UnificationFailed:
            if not we_are_translated():
                if fcont.is_done():
                    raise
            scont, fcont, heap = fcont.fail(heap)
        except error.CatchableError, e:
            scont, fcont, heap = scont.engine.throw(e.term, scont, fcont, heap)
    assert isinstance(scont, DoneContinuation)
    if scont.failed:
        raise error.UnificationFailed

class Engine(object):
    def __init__(self):
        self.parser = None
        self.operations = None
        from prolog.builtin.statistics import Clocks
        self.clocks = Clocks()
        self.clocks.startup()
    # _____________________________________________________
    # database functionality

    def get_function(self, signature):
        return signature.get_extra_engine_local("function", self)

    def add_rule(self, rule, end=True):
        if helper.is_term(rule):
            assert isinstance(rule, Callable)
            if rule.signature().eq(predsig):
                rule = Rule(rule.argument_at(0), rule.argument_at(1))
            else:
                rule = Rule(rule, None)
        elif isinstance(rule, Atom):
            rule = Rule(rule, None)
        else:
            error.throw_type_error("callable", rule)
            assert 0, "unreachable" # make annotator happy
        signature = rule.signature        
        if self.get_builtin(signature):
            error.throw_permission_error(
                "modify", "static_procedure", rule.head.get_prolog_signature())
        function = self._lookup(signature)
        
        function.add_rule(rule, end)

    @jit.purefunction_promote("0")
    def get_builtin(self, signature):
        from prolog import builtin # for the side-effects
        return signature.get_extra("builtin")

    @jit.purefunction_promote("0")
    def _lookup(self, signature):
        assert signature.cached
        function = self.get_function(signature)
        if function is None:
            function = Function()
            signature.set_extra_engine_local("function", function, self)
        return function

    # _____________________________________________________
    # parsing-related functionality

    def _build_and_run(self, tree):
        from prolog.interpreter.parsing import TermBuilder
        builder = TermBuilder()
        term = builder.build_query(tree)
        if isinstance(term, Term) and term.signature().eq(callsig):
            self.run(term.argument_at(0))
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
        if continuation is None:
            continuation = DoneContinuation(self)
        driver(*self.call(query, continuation, DoneContinuation(self), Heap()))
    run = run_query

    def call(self, query, scont, fcont, heap):
        if not isinstance(query, Callable):
            raise error.throw_type_error('callable', query)
        signature = query.signature()        
        builtin = self.get_builtin(signature)
        if builtin is not None:
            return self.continue_(BuiltinContinuation(self, scont, builtin, query), fcont, heap)

        # do a real call
        function = self._lookup(signature)
        startrulechain = jit.hint(function.rulechain, promote=True)
        if startrulechain is None:
            return error.throw_existence_error(
                "procedure", query.get_prolog_signature())
        rulechain = startrulechain.find_applicable_rule(query)
        if rulechain is None:
            raise error.UnificationFailed
        scont = UserCallContinuation(self, scont, query,
                                     rulechain)
        return self.continue_(scont, fcont, heap)

    # _____________________________________________________
    # error handling

    @jit.unroll_safe
    def throw(self, exc, scont, fcont, heap):
        # XXX write tests for catching non-ground things
        while not scont.is_done():
            if not isinstance(scont, CatchingDelimiter):
                scont = scont.nextcont
                continue
            discard_heap = scont.heap
            heap = heap.revert_upto(discard_heap)
            try:
                scont.catcher.unify(exc, heap)
            except error.UnificationFailed:
                scont = scont.nextcont
            else:
                # XXX discard the heap?
                return self.call(
                    scont.recover, scont.nextcont, scont.fcont, heap)
        raise error.UncaughtError(exc)


    @specialize.argtype(0)
    def continue_(scont, fcont, heap):
        if scont.is_done() or isinstance(scont, RuleContinuation) and scont._rule.body is not None:
            return scont, fcont, heap
        try:
            return scont.activate(fcont, heap)
        except error.UnificationFailed:
            if not we_are_translated():
                if fcont.is_done():
                    raise
            return fcont.fail(heap)
        except error.CatchableError, e:
            return scont.engine.throw(e.term, scont, fcont, heap)
    continue_._always_inline_ = True
    continue_ = staticmethod(continue_)

    def __freeze__(self):
        return True

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

    def is_done(self):
        return False

    def find_end_of_cut(self):
        return self.nextcont.find_end_of_cut()

    def _dot(self, seen):
        if self in seen:
            return
        seen.add(self)
        yield '%s [label="%s", shape=box]' % (id(self), repr(self)[:50])
        if self.nextcont is not None:
            yield "%s -> %s [label=nextcont]" % (id(self), id(self.nextcont))
            for line in self.nextcont._dot(seen):
                yield line

def view(*objects):
    from dotviewer import graphclient
    content = ["digraph G{"]
    seen = set()
    for obj in objects:
        content.extend(obj._dot(seen))
    content.append("}")
    p = py.test.ensuretemp("prolog").join("temp.dot")
    p.write("\n".join(content))
    graphclient.display_dot_file(str(p))

class FailureContinuation(Continuation):
    """ A continuation that can represent failures. It has a .fail method that
    is called to prepare it for being used as a failure continuation.
    
    NB: a Continuation can be used both as a failure continuation and as a
    success continuation."""

    def fail(self, heap):
        """ Needs to be called to prepare the object as being used as a failure
        continuation. After fail has been called, the continuation will usually
        be activated. Particularly useful for objects that are both a regular
        and a failure continuation, to distinguish the two cases. """
        # returns (next cont, failure cont, heap)
        raise NotImplementedError("abstract base class")

    def cut(self, heap):
        """ Cut away choice points till the next correct cut delimiter.
        Slightly subtle. """
        return self

class DoneContinuation(FailureContinuation):
    def __init__(self, engine):
        Continuation.__init__(self, engine, None)
        self.failed = False

    def activate(self, fcont, heap):
        assert 0, "unreachable"

    def fail(self, heap):
        self.failed = True
        return self, self, heap

    def is_done(self):
        return True

    def find_end_of_cut(self):
        return DoneContinuation(self.engine)

class BodyContinuation(Continuation):
    """ Represents a bit of Prolog code that is still to be called. """
    def __init__(self, engine, nextcont, body):
        Continuation.__init__(self, engine, nextcont)
        self.body = body

    def activate(self, fcont, heap):
        return self.engine.call(self.body, self.nextcont, fcont, heap)

    def __repr__(self):
        return "<BodyContinuation %r>" % (self.body, )

class BuiltinContinuation(Continuation):
    """ Rerpresents the call to a builtin. """
    def __init__(self, engine, nextcont, builtin, query):
        Continuation.__init__(self, engine, nextcont)
        self.builtin = builtin
        self.query = query

    def activate(self, fcont, heap):
        return self.builtin.call(self.engine, self.query, self.nextcont, fcont, heap)

    def __repr__(self):
        return "<BuiltinContinuation %r, %r>" % (self.builtin, self.query, )

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
        heap = heap.revert_upto(self.undoheap, discard_choicepoint=True)
        return self.engine.continue_(self, self.orig_fcont, heap)

    def cut(self, heap):
        heap = self.undoheap.discard(heap)
        return self.orig_fcont.cut(heap)

    def _dot(self, seen):
        if self in seen:
            return
        for line in FailureContinuation._dot(self, seen):
            yield line
        seen.add(self)
        if self.orig_fcont is not None:
            yield "%s -> %s [label=orig_fcont]" % (id(self), id(self.orig_fcont))
            for line in self.orig_fcont._dot(seen):
                yield line
        if self.undoheap is not None:
            yield "%s -> %s [label=heap]" % (id(self), id(self.undoheap))
            for line in self.undoheap._dot(seen):
                yield line

class UserCallContinuation(ChoiceContinuation):
    def __init__(self, engine, nextcont, query, rulechain):
        ChoiceContinuation.__init__(self, engine, nextcont)
        self.query = query
        self.rulechain = rulechain

    def activate(self, fcont, heap):
        rulechain = jit.hint(self.rulechain, promote=True)
        rule = rulechain
        nextcont = self.nextcont
        if rule.contains_cut:
            nextcont = CutScopeNotifier.insert_scope_notifier(
                    self.engine, nextcont, fcont)
        query = self.query
        restchain = rulechain.find_next_applicable_rule(query)
        if restchain is not None:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.rulechain = restchain

        cont = RuleContinuation(self.engine, nextcont, rule, query)
        return cont, fcont, heap

    def __repr__(self):
        return "<UserCallContinuation query=%r rule=%r>" % (
                self.query, self.rulechain)
    

class RuleContinuation(Continuation):
    """ A Continuation that represents the application of a rule, i.e.:
        - standardizing apart of the rule
        - unifying the rule head with the query
        - calling the body of the rule
    """

    def __init__(self, engine, nextcont, rule, query):
        Continuation.__init__(self, engine, nextcont)
        self._rule = rule
        self.query = query

    def activate(self, fcont, heap):
        nextcont = self.nextcont
        rule = jit.hint(self._rule, promote=True)
        nextcall = rule.clone_and_unify_head(heap, self.query)
        if nextcall is not None:
            return self.engine.call(nextcall, nextcont, fcont, heap)
        else:
            cont = nextcont
        return cont, fcont, heap

    def __repr__(self):
        return "<RuleContinuation rule=%r query=%r>" % (self._rule, self.query)

class CutScopeNotifier(Continuation):
    def __init__(self, engine, nextcont, fcont_after_cut):
        Continuation.__init__(self, engine, nextcont)
        self.fcont_after_cut = fcont_after_cut

    @staticmethod
    def insert_scope_notifier(engine, nextcont, fcont):
        if isinstance(nextcont, CutScopeNotifier) and nextcont.fcont_after_cut is fcont:
            return nextcont
        return CutScopeNotifier(engine, nextcont, fcont)

    def find_end_of_cut(self):
        return self.fcont_after_cut

    def activate(self, fcont, heap):
        return self.nextcont, fcont, heap

    def _dot(self, seen):
        if self in seen:
            return
        for line in Continuation._dot(self, seen):
            yield line
        seen.add(self)
        yield "%s -> %s [label=fcont_after_cut]" % (id(self), id(self.fcont_after_cut))
        for line in self.nextcont._dot(seen):
            yield line


class CatchingDelimiter(Continuation):
    def __init__(self, engine, nextcont, fcont, catcher, recover, heap):
        Continuation.__init__(self, engine, nextcont)
        self.catcher = catcher
        self.recover = recover
        self.fcont = fcont
        self.heap = heap

    def activate(self, fcont, heap):
        return self.nextcont, fcont, heap

    def _dot(self, seen):
        if self in seen:
            return
        for line in Continuation._dot(self, seen):
            yield line
        if self.heap is not None:
            yield "%s -> %s [label=heap]" % (id(self), id(self.heap))
            for line in self.heap._dot(seen):
                yield line
