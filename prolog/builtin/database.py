import py
from prolog.interpreter import helper, term, error
from prolog.interpreter.signature import Signature
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# database

@expose_builtin("abolish", unwrap_spec=["obj"])
def impl_abolish(engine, heap, predicate):
    name, arity = helper.unwrap_predicate_indicator(predicate)
    if arity < 0:
        error.throw_domain_error("not_less_than_zero", term.Number(arity))
    signature = Signature.getsignature(name, arity)
    if signature.get_extra("builtin"):
        error.throw_permission_error("modify", "static_procedure",
                                     predicate)
    function = engine.get_function(signature)
    if function is not None:
        function.rulechain = None

@expose_builtin(["assert", "assertz"], unwrap_spec=["callable"])
def impl_assert(engine, heap, rule):
    engine.add_rule(rule.getvalue(heap))

@expose_builtin("asserta", unwrap_spec=["callable"])
def impl_asserta(engine, heap, rule):
    engine.add_rule(rule.getvalue(heap), end=False)


@expose_builtin("retract", unwrap_spec=["callable"])
def impl_retract(engine, heap, pattern):
    if helper.is_term(pattern) and pattern.name()== ":-":
        head = helper.ensure_callable(pattern.argument_at(0))
        body = helper.ensure_callable(pattern.argument_at(1))
    else:
        head = pattern
        body = None
    if head.signature().get_extra("builtin"):
        assert isinstance(head, term.Callable)
        error.throw_permission_error("modify", "static_procedure", 
                                     head.get_prolog_signature())
    function = engine.get_function(head.signature())
    if function is None:
        raise error.UnificationFailed
    rulechain = function.rulechain
    oldstate = heap.branch()
    while rulechain:
        rule = rulechain
        # standardizing apart
        try:
            deleted_body = rule.clone_and_unify_head(heap, head)
            if body is not None:
                body.unify(deleted_body, heap)
        except error.UnificationFailed:
            oldstate.revert_upto(heap)
        else:
            if function.rulechain is rulechain:
                function.rulechain = rulechain.next
            else:
                function.remove(rulechain)
            break
        rulechain = rulechain.next
    else:
        raise error.UnificationFailed()
    # heap.discard(oldstate)



