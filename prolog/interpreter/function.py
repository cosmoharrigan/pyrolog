# XXX needs tests

class LinkedRules(object):
    _immutable_ = True
    def __init__(self, rule, next=None):
        self.rule = rule
        self.next = next

    def copy(self, stopat=None):
        first = LinkedRules(self.rule)
        curr = self.next
        copy = first
        while curr is not stopat:
            # if this is None, the stopat arg was invalid
            assert curr is not None
            new = LinkedRules(curr.rule)
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

    def __repr__(self):
        return "LinkedRules(%r, %r)" % (self.rule, self.next)



class Function(object):
    def __init__(self, firstrule=None):
        if firstrule is None:
            self.rulechain = self.last = None
        else:
            self.rulechain = LinkedRules(firstrule)
            self.last = self.rulechain

    def add_rule(self, rule, atend):
        if self.rulechain is None:
            self.rulechain = self.last = LinkedRules(rule)
        elif atend:
            self.rulechain, last = self.rulechain.copy()
            self.last = LinkedRules(rule)
            last.next = self.last
        else:
            self.rulechain = LinkedRules(rule, self.rulechain)

    def remove(self, rulechain):
        self.rulechain, last = self.rulechain.copy(rulechain)
        last.next = rulechain.next

