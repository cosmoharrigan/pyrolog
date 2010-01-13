import py
from pypy.rlib import jit
from prolog.interpreter import error
from prolog.interpreter.term import Term, Atom, Var, Callable
from prolog.interpreter.function import Function, Rule

# ___________________________________________________________________
# JIT stuff

def can_inline(*args):
    return False

def get_printable_location(rule):
    if rule:
        s = rule.signature
    else:
        s = "No rule"
    return s

def get_jitcell_at(where, rule):
    # XXX can be vastly simplified
    return rule.jit_cells.get(where, None)

def set_jitcell_at(newcell, where, rule):
    # XXX can be vastly simplified
    rule.jit_cells[where] = newcell


jitdriver = jit.JitDriver(
        greens=["rule"],
        reds=["scont", "fcont", "heap"],
        can_inline=can_inline,
        get_printable_location=get_printable_location,
        #get_jitcell_at=get_jitcell_at,
        #set_jitcell_at=set_jitcell_at,
        )

# ___________________________________________________________________
# end JIT stuff


def driver(scont, fcont, heap):
    oldrule = scont.rule
    while not scont.is_done():
        rule = scont.rule
        if rule is None:
            rule = oldrule
        else:
            oldrule = rule
        try:
            jitdriver.jit_merge_point(rule=rule, scont=scont, fcont=fcont,
                                      heap=heap)
            scont, fcont, heap  = scont.activate(fcont, heap)
        except error.UnificationFailed:
            scont, fcont, heap = fcont.fail(heap)
        except error.CatchableError, e:
            scont, fcont, heap = scont.engine.throw(e.term, scont, fcont, heap)
    assert isinstance(scont, DoneContinuation)
    if scont.failed:
        raise error.UnificationFailed


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
        if continuation is None:
            continuation = DoneContinuation(self)
        driver(*self.call(query, continuation, DoneContinuation(self), Heap()))
    run = run_query

    def call(self, query, scont, fcont, heap):
        if not isinstance(query, Callable):
            raise Exception
        signature = query.signature
        builtin = self.get_builtin(signature)
        if builtin is not None:
            return BuiltinContinuation(self, scont, builtin, query), fcont, heap

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
        return scont, fcont, heap

    # _____________________________________________________
    # error handling

    def throw(self, exc, scont, fcont, heap):
        # XXX write tests for catching non-ground things
        while not scont.is_done():
            if not isinstance(scont, CatchingDelimiter):
                scont = scont.nextcont
                continue
            heap = heap.revert_upto(scont.heap)
            try:
                scont.catcher.unify(exc, heap)
            except error.UnificationFailed:
                scont = scont.nextcont
            else:
                # XXX discard the heap?
                return self.call(
                    scont.recover, scont.nextcont, scont.fcont, heap)
        raise error.UncaughtError(exc)

#    def throw_system_error(self, term, scont, fcont, heap):
#        term = Term("error", [term])
#        return self.throw(term, scont, fcont, heap)
#
#    def throw_existence_error(self, object_type, obj, scont, fcont, heap):
#        term = Term("existence_error", [Atom.newatom(object_type), obj])
#        return self.throw_system_error(term, scont, fcont, heap)
#
#    def throw_instantiation_error(self, scont, fcont, heap):
#        term = Atom.newatom("instantiation_error")
#        return self.throw_system_error(term, scont, fcont, heap)
#
#    def throw_type_error(self, valid_type, obj, scont, fcont, heap):
#        # valid types are:
#        # atom, atomic, byte, callable, character
#        # evaluable, in_byte, in_character, integer, list
#        # number, predicate_indicator, variable
#        term = Term("type_error", [Atom.newatom(valid_type), obj])
#        return self.throw_system_error(term, scont, fcont, heap)
#
#    def throw_domain_error(self, valid_domain, obj, scont, fcont, heap):
#        # valid domains are:
#        # character_code_list, close_option, flag_value, io_mode,
#        # not_empty_list, not_less_than_zero, operator_priority,
#        # operator_specifier, prolog_flag, read_option, source_sink,
#        # stream, stream_option, stream_or_alias, stream_position,
#        # stream_property, write_option
#        term = Term("domain_error", [Atom.newatom(valid_domain), obj])
#        return self.throw_system_error(term, scont, fcont, heap)
#
#    def throw_permission_error(self, operation, permission_type, obj, scont, fcont, heap):
#        # valid operations are:
#        # access, create, input, modify, open, output, reposition 
#
#        # valid permission_types are:
#        # binary_stream, flag, operator, past_end_of_stream, private_procedure,
#        # static_procedure, source_sink, stream, text_stream. 
#        term = Term("permission_error", [term.Atom.newatom(operation),
#                                         term.Atom.newatom(permission_type),
#                                         obj])
#        return self.throw_system_error(term, scont, fcont, heap)


# ___________________________________________________________________
# Heap implementation

class Heap(object):
    INITSIZE = 10
    def __init__(self, prev=None):
        self.trail_var = [None] * Heap.INITSIZE
        self.trail_binding = [None] * Heap.INITSIZE
        self.i = 0
        self.prev = prev

    # _____________________________________________________
    # interface that term.py uses

    def add_trail(self, var):
        """ Remember the current state of a variable to be able to backtrack it
        to that state. Usually called just before a variable changes. """
        if self.i >= len(self.trail_var):
            self._double_size()
        self.trail_var[self.i] = var
        self.trail_binding[self.i] = var.binding
        self.i += 1

    def _double_size(self):
        trail_var = [None] * (len(self.trail_var) * 2)
        trail_binding = [None] * len(trail_var)
        for i in range(self.i):
            trail_var[i] = self.trail_var[i]
            trail_binding[i] = self.trail_binding[i]
        self.trail_var = trail_var
        self.trail_binding = trail_binding

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

    @jit.unroll_safe
    def revert_upto(self, heap):
        """ Revert to the heap corresponding to a choice point. The return
        value is the new heap that should be used."""
        previous = self
        while self is not heap:
            self._revert()
            previous = self
            self = self.prev
        return previous

    @jit.unroll_safe
    def _revert(self):
        for i in range(self.i):
            self.trail_var[i].binding = self.trail_binding[i]
            self.trail_var[i] = None
            self.trail_binding[i] = None
        self.i = 0

# ___________________________________________________________________
# Continuation classes

class Continuation(object):
    """ Represents a continuation of the Prolog computation. This can be seen
    as an RPython-compatible way to express closures. """

    rule = None
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

    def _dot(self):
        yield '%s [label="%r", shape=box]' % (id(self), self)
        if self.nextcont is not None:
            yield "%s -> %s [label=nextcont]" % (id(self), id(self.nextcont))
            for line in self.nextcont._dot():
                yield line

    def view(self):
        from dotviewer import graphclient
        content = ["digraph G{"]
        content.extend(self._dot())
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

    def cut(self):
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
        heap = heap.revert_upto(self.undoheap)
        return self, self.orig_fcont, self.undoheap

    def cut(self):
        assert self.undoheap is not None
        return self.orig_fcont.cut()

    def _dot(self):
        for line in FailureContinuation._dot(self):
            yield line
        if self.orig_fcont is not None:
            yield "%s -> %s [label=orig_fcont]" % (id(self), id(self.orig_fcont))
            for line in self.orig_fcont._dot():
                yield line

class UserCallContinuation(ChoiceContinuation):
    def __init__(self, engine, nextcont, query, rulechain):
        ChoiceContinuation.__init__(self, engine, nextcont)
        self.query = query
        signature = query.signature
        self.rulechain = rulechain

    def activate(self, fcont, heap):
        rulechain = jit.hint(self.rulechain, promote=True)
        rule = rulechain
        nextcont = self.nextcont
        if rule.contains_cut:
            nextcont = fcont = CutDelimiter(self.engine, nextcont, fcont)
        query = self.query
        restchain = rulechain.find_next_applicable_rule(query)
        if restchain is not None:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.rulechain = restchain
        cont = RuleContinuation(self.engine, nextcont, rule, query)
        return cont, fcont, heap

    def __repr__(self):
        return "<UserCallContinuation query=%r rule=%r>" % (
                self.query, self.rulechain.rule, )
    

class RuleContinuation(Continuation):
    """ A Continuation that represents the application of a rule, i.e.:
        - standardizing apart of the rule
        - unifying the rule head with the query
        - calling the body of the rule
    """

    def __init__(self, engine, nextcont, rule, query):
        Continuation.__init__(self, engine, nextcont)
        self.rule = rule
        self.query = query

    def activate(self, fcont, heap):
        nextcont = self.nextcont
        nextcall = self.rule.clone_and_unify_head(heap, self.query)
        if nextcall is not None:
            # note that it is ok to put the can_enter_jit here in the middle of the
            # function: jumping from here back to the driver loop won't change the
            # semantics
            jitdriver.can_enter_jit(rule=self.rule, scont=self, fcont=fcont,
                                    heap=heap)
            cont = BodyContinuation(self.engine, nextcont, nextcall)
        else:
            cont = nextcont
        return cont, fcont, heap

    def __repr__(self):
        return "<RuleContinuation rule=%r query=%r>" % (self.rule, self.query)

class CutDelimiter(FailureContinuation):
    def __init__(self, engine, nextcont, fcont):
        FailureContinuation.__init__(self, engine, nextcont)
        self.fcont = fcont
        self.activated = False

    def activate(self, fcont, heap):
        self.activated = True
        return self.nextcont, fcont, heap

    def fail(self, heap):
        self.activated = False
        return self.fcont.fail(heap)

    def cut(self):
        if not self.activated:
            return self
        return self.fcont.cut()


    def __repr__(self):
        return "<CutDelimiter activated=%r>" % (self.activated, )

    def _dot(self):
        for line in FailureContinuation._dot(self):
            yield line
        yield "%s -> %s [label=fcont]" % (id(self), id(self.fcont))
        for line in self.fcont._dot():
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
