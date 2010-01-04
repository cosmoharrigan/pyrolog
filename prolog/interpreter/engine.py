from prolog.interpreter.term import Var, Term, Rule, Atom, debug_print, \
    Callable
from prolog.interpreter.function import Function
from prolog.interpreter.error import UnificationFailed, CutException
from prolog.interpreter import error
from pypy.rlib import jit

DEBUG = False

# bytecodes:
CALL = 0
USER_CALL = 1
TRY_RULE = 2
CONTINUATION = 3
DONE = 4


class Continuation(object):
    def call(self, engine, choice_point=True):
        if choice_point:
            return engine.main_loop(CONTINUATION, None, self, None)
        return (CONTINUATION, None, self, None)

    def _call(self, engine):
        return (DONE, None, None, None)

DONOTHING = Continuation()

class LimitedScopeContinuation(Continuation):
    def __init__(self, continuation):
        self.scope_active = True
        self.continuation = continuation

    def _call(self, engine):
        self.scope_active = False
        return self.continuation.call(engine, choice_point=False)


class TrailHolder(object):
    CHUNKSIZE = 20
    def __init__(self, heap):
        self.heap = heap
        self.trailvars = [None] * self.CHUNKSIZE
        self.trailbindings = [None] * self.CHUNKSIZE
        self.i = 0
        self.prev = heap.current
        heap.current = self
        self.is_choice = False

    def add_trail(self, var):
        if self.i < len(self.trailvars):
            self.trailvars[self.i] = var
            self.trailbindings[self.i] = var.binding
            self.i += 1
            return
        newtrail = self.heap.newtrail()
        newtrail.add_trail(var)

    @jit.unroll_safe
    def revert(self):
        for index in range(self.i):
            self.trailvars[index].binding = self.trailbindings[index]
        self.i = 0

    @jit.unroll_safe
    def last_choice(self):
        while self is not None and not self.is_choice:
            self = self.prev
        return self


class Heap(object):
    current = None
    def __init__(self):
        self.newtrail()

    def last_choice(self):
        return self.current.last_choice()

    def newtrail(self):
        self.current = result = TrailHolder(self)
        return result

    def add_trail(self, var):
        # var was created after the currently active choice point
        # which means that on backtracking, var will not even exist
        # this makes trailing not necessary
        created_after = var.created_after_choice_point
        if created_after:
            created_after = created_after.last_choice()
        if created_after is self.last_choice():
            return
        self.current.add_trail(var)

    def branch(self):
        res = self.current
        res.is_choice = True
        self.newtrail()
        return res

    @jit.unroll_safe
    def revert(self, state):
        assert state.is_choice
        old = state
        curr = self.current
        while curr is not state:
            curr.revert()
            old = curr
            curr = curr.prev
        self.current = old

    @jit.unroll_safe
    def discard(self, state):
        # XXX check all calls to .branch in the code have a matching call to
        # .discard
        state.is_choice = False
        while (self.current.i == 0 and self.current is not state):
            assert not self.current.prev.is_choice
            self.current = self.current.prev

    def newvar(self):
        result = Var()
        result.created_after_choice_point = self.current.last_choice()
        return result

    def revert_and_discard(self, state):
        self.revert(state)
        self.discard(state)

# ___________________________________________________________________
# JIT stuff

def can_inline(where, rule):
    if rule is None:
        return True
    if rule.body is None:
        return True
    return False # XXX for now!

def get_printable_location(where, rule):
    if rule:
        s = rule.signature
    else:
        s = "No rule"
    return "%s: %s" % (where, s)

def leave(where, rule, self, query, continuation):
    pass

def get_jitcell_at(where, rule):
    # XXX can be vastly simplified
    return rule.jit_cells.get(where, None)

def set_jitcell_at(newcell, where, rule):
    # XXX can be vastly simplified
    rule.jit_cells[where] = newcell


jitdriver = jit.JitDriver(
        greens=["where", "rule"],
        reds=["self", "query", "continuation"],
        can_inline=can_inline,
        get_printable_location=get_printable_location,
        leave=leave,
        #get_jitcell_at=get_jitcell_at,
        #set_jitcell_at=set_jitcell_at,
        )

# ___________________________________________________________________
# end JIT stuff


class Engine(object):
    def __init__(self):
        self.heap = Heap()
        self.signature2function = {}
        self.parser = None
        self.operations = None

    def add_rule(self, rule, end=True):
        from prolog import builtin
        if DEBUG:
            debug_print("add_rule", rule)
        if isinstance(rule, Term):
            if rule.name == ":-":
                rule = Rule(rule.args[0], rule.args[1])
            else:
                rule = Rule(rule, None)
            signature = rule.signature
        elif isinstance(rule, Atom):
            rule = Rule(rule, None)
            signature = rule.signature
        else:
            error.throw_type_error("callable", rule)
            assert 0, "unreachable" # make annotator happy
        if signature in builtin.builtins:
            error.throw_permission_error(
                "modify", "static_procedure", rule.head.get_prolog_signature())
        function = self._lookup(signature)
        function.add_rule(rule, end)

    def run(self, query, continuation=DONOTHING):
        if not isinstance(query, Callable):
            error.throw_type_error("callable", query)
        try:
            return self.call(query, continuation, choice_point=True)
        except CutException, e:
            return self.continue_after_cut(e.continuation)

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

    def call(self, query, continuation=DONOTHING, choice_point=True):
        assert isinstance(query, Callable)
        if not choice_point:
            return (CALL, query, continuation, None)
        return self.main_loop(CALL, query, continuation)

    @jit.purefunction_promote
    def get_builtin(self, signature):
        from prolog.builtin import builtins
        builtin = builtins.get(signature, None)
        return builtin

    def _call(self, query, continuation):
        signature = query.signature
        builtin = self.get_builtin(signature)
        if builtin is not None:
            return builtin.call(self, query, continuation)
        # do a real call
        return self.user_call(query, continuation, choice_point=False)

    def main_loop(self, where, query, continuation, rule=None):
        while 1:
            jitdriver.jit_merge_point(self=self, where=where, query=query,
                                      continuation=continuation, rule=rule)
            if where == DONE:
                return (DONE, None, None, None)
            next = self.dispatch_bytecode(where, query, continuation, rule)
            where, query, continuation, rule = next

    def dispatch_bytecode(self, where, query, continuation, rule):
        if where == CALL:
            next = self._call(query, continuation)
        elif where == TRY_RULE:
            next = self._try_rule(rule, query, continuation)
        elif where == USER_CALL:
            next = self._user_call(query, continuation)
            where, query, continuation, rule = next
            jitdriver.can_enter_jit(self=self, where=where, query=query,
                                    continuation=continuation, rule=rule)
        elif where == CONTINUATION:
            next = continuation._call(self)
        else:
            raise Exception("unknown bytecode")
        return next

    @jit.purefunction
    def _lookup(self, signature):
        signature2function = self.signature2function
        function = signature2function.get(signature, None)
        if function is None:
            signature2function[signature] = function = Function()
        return function

    def user_call(self, query, continuation, choice_point=True):
        if not choice_point:
            return (USER_CALL, query, continuation, None)
        return self.main_loop(USER_CALL, query, continuation)

    @jit.unroll_safe
    def _user_call(self, query, continuation):
        signature = query.signature
        function = self._lookup(signature)
        startrulechain = jit.hint(function.rulechain, promote=True)
        if startrulechain is None:
            error.throw_existence_error(
                "procedure", query.get_prolog_signature())

        rulechain = startrulechain.find_applicable_rule(query)
        if rulechain is None:
            # none of the rules apply
            raise UnificationFailed()
        oldstate = self.heap.branch()
        while 1:
            rule = rulechain.rule
            rulechain = rulechain.find_next_applicable_rule(query)
            choice_point = rulechain is not None
            if rule.contains_cut:
                continuation = LimitedScopeContinuation(continuation)
                try:
                    result = self.try_rule(rule, query, continuation)
                    self.heap.discard(oldstate)
                    return result
                except UnificationFailed:
                    self.heap.revert(oldstate)
                except CutException, e:
                    if continuation.scope_active:
                        return self.continue_after_cut(e.continuation,
                                                       continuation)
                    raise
            else:
                try:
                    # for the last rule (rulechain is None), this will always
                    # return immediately, because choice_point is False
                    result = self.try_rule(rule, query, continuation,
                                           choice_point=choice_point)
                    self.heap.discard(oldstate)
                    return result
                except UnificationFailed:
                    assert choice_point
                    self.heap.revert(oldstate)

    def try_rule(self, rule, query, continuation=DONOTHING, choice_point=True):
        if not choice_point:
            return (TRY_RULE, query, continuation, rule)
        return self.main_loop(TRY_RULE, query, continuation, rule)

    def _try_rule(self, rule, query, continuation):
        # standardizing apart
        nextcall = rule.clone_and_unify_head(self.heap, query)
        if nextcall is not None:
            return self.call(nextcall, continuation, choice_point=False)
        else:
            return continuation.call(self, choice_point=False)

    def continue_after_cut(self, continuation, lsc=None):
        while 1:
            try:
                return continuation.call(self, choice_point=True)
            except CutException, e:
                if lsc is not None and not lsc.scope_active:
                    raise
                continuation = e.continuation

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




from prolog.interpreter.continuation import Heap, Engine, Continuation
