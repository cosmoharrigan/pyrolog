from prolog.interpreter.function import LinkedRules, Function

def test_copy():
    l1 = LinkedRules(1, LinkedRules(2, LinkedRules(3)))
    l1c, _ = l1.copy()

    t1 = l1
    t2 = l1c
    while t1 is not None:
        assert t1.rule == t2.rule
        assert t1 is not t2
        t1 = t1.next
        t2 = t2.next

    l0 = LinkedRules(-1, LinkedRules(-2, LinkedRules(-3, l1)))
    l0c, end = l0.copy(l1)
    t1 = l0
    t2 = l0c
    while t1 is not l1:
        assert t1.rule == t2.rule
        assert t1 is not t2
        t1 = t1.next
        prev = t2
        t2 = t2.next
    assert t2 is None
    assert prev is end
    
def test_function():
    def get_rules(chain):
        r = []
        while chain:
            r.append(chain.rule)
            chain = chain.next
        return r
    f = Function()
    f.add_rule(1, True)
    assert get_rules(f.rulechain) == [1]
    f.add_rule(2, True)
    assert get_rules(f.rulechain) == [1, 2]
    f.add_rule(0, False)
    assert get_rules(f.rulechain) == [0, 1, 2]

    # test logical update view
    rulechain = f.rulechain
    f.add_rule(15, True)
    assert get_rules(rulechain) == [0, 1, 2]
    assert get_rules(f.rulechain) == [0, 1, 2, 15]
