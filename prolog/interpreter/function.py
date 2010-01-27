from prolog.interpreter.term import Atom, Callable, Term
from pypy.rlib import jit, objectmodel, unroll
# XXX needs tests

class Rule(object):
    _immutable_ = True
    _immutable_fields_ = ["headargs[*]"]
    _attrs_ = ['next', 'head', 'headargs', 'contains_cut', 'body', 'size_env', 'signature']
    unrolling_attrs = unroll.unrolling_iterable(_attrs_)
    
    def __init__(self, head, body, next = None):
        from prolog.interpreter import helper
        assert isinstance(head, Callable)
        memo = {}
        self.head = h = head.enumerate_vars(memo)
        if isinstance(h, Term):
            self.headargs = h.arguments()
        else:
            self.headargs = None
        if body is not None:
            body = helper.ensure_callable(body)
            self.body = body.enumerate_vars(memo)
        else:
            self.body = None
        self.size_env = len(memo)
        self.signature = head.signature
        self._does_contain_cut()

        self.next = next

    def _does_contain_cut(self):
        if self.body is None:
            self.contains_cut = False
            return
        stack = [self.body]
        while stack:
            current = stack.pop()
            if isinstance(current, Atom):
                if current.name == "!":
                    self.contains_cut = True
                    return
            elif isinstance(current, Term):
                stack.extend(current.arguments())
        self.contains_cut = False

    @jit.unroll_safe
    def clone_and_unify_head(self, heap, head):
        env = [None] * self.size_env
        if self.headargs is not None:
            assert isinstance(head, Term)
            for i in range(len(self.headargs)):
                arg2 = self.headargs[i]
                arg1 = head.argument_at(i)
                arg2.unify_and_standardize_apart(arg1, heap, env)
        body = self.body
        if body is None:
            return None
        return body.copy_standardize_apart(heap, env)

    def __repr__(self):
        if self.body is None:
            return "%s." % (self.head, )
        return "%s :- %s." % (self.head, self.body)

    def instance_copy(self):
        other = objectmodel.instantiate(Rule)
        for f in Rule.unrolling_attrs:
            setattr(other, f, getattr(self, f))
        return other
        
    def copy(self, stopat=None):
        first = self.instance_copy()
        curr = self.next
        copy = first
        while curr is not stopat:
            # if this is None, the stopat arg was invalid
            assert curr is not None
            new = curr.instance_copy()
            copy.next = new
            copy = new
            curr = curr.next
        return first, copy

    def find_applicable_rule(self, query):
        # This method should do some quick filtering on the rules to filter out
        # those that cannot match query. Here is where e.g. indexing should
        # occur. For now, we just return all rules, which is clearly not
        # optimal. XXX improve this
        return self

    def find_next_applicable_rule(self, query):
        if self.next is None:
            return None
        return self.next.find_applicable_rule(query)
    
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__dict__ == other.__dict__
    def __ne__(self, other):
        return not self == other


class Function(object):
    def __init__(self, firstrule=None):
        if firstrule is None:
            self.rulechain = self.last = None
        else:
            self.rulechain = Rule(firstrule)
            self.last = self.rulechain

    def add_rule(self, rule, atend):
        if self.rulechain is None:
            self.rulechain = self.last = rule
        elif atend:
            self.rulechain, last = self.rulechain.copy()
            self.last = rule
            last.next = self.last
        else:
            rule.next = self.rulechain
            self.rulechain = rule

    def remove(self, rulechain):
        self.rulechain, last = self.rulechain.copy(rulechain)
        last.next = rulechain.next

