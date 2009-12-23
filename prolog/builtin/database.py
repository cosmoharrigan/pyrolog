import py
from prolog.interpreter import engine, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# database

@expose_builtin("abolish", unwrap_spec=["obj"])
def impl_abolish(engine, heap, predicate):
    from prolog.builtin import builtins
    name, arity = helper.unwrap_predicate_indicator(predicate)
    if arity < 0:
        error.throw_domain_error("not_less_than_zero", term.Number(arity))
    signature = name + "/" + str(arity)
    if signature in builtins:
        error.throw_permission_error("modify", "static_procedure",
                                     predicate)
    if signature in engine.signature2function:
        del engine.signature2function[signature]

@expose_builtin(["assert", "assertz"], unwrap_spec=["callable"])
def impl_assert(engine, heap, rule):
    engine.add_rule(rule.getvalue(heap))

@expose_builtin("asserta", unwrap_spec=["callable"])
def impl_asserta(engine, heap, rule):
    engine.add_rule(rule.getvalue(heap), end=False)


@expose_builtin("retract", unwrap_spec=["callable"])
def impl_retract(engine, heap, pattern):
    from prolog.builtin import builtins
    if isinstance(pattern, term.Term) and pattern.name == ":-":
        head = helper.ensure_callable(pattern.args[0])
        body = helper.ensure_callable(pattern.args[1])
    else:
        head = pattern
        body = None
    if head.signature in builtins:
        assert isinstance(head, term.Callable)
        error.throw_permission_error("modify", "static_procedure", 
                                     head.get_prolog_signature())
    function = engine.signature2function.get(head.signature, None)
    if function is None:
        raise error.UnificationFailed
    #import pdb; pdb.set_trace()
    rulechain = function.rulechain
    oldstate = heap.branch()
    while rulechain:
        rule = rulechain.rule
        # standardizing apart
        try:
            deleted_body = rule.clone_and_unify_head(heap, head)
            if body is not None:
                body.unify(deleted_body, heap)
        except error.UnificationFailed:
            heap.revert(oldstate)
        else:
            if function.rulechain is rulechain:
                if rulechain.next is None:
                    del engine.signature2function[head.signature]
                else:
                    function.rulechain = rulechain.next
            else:
                function.remove(rulechain)
            break
        rulechain = rulechain.next
    else:
        raise error.UnificationFailed()
    heap.discard(oldstate)



