import py
from prolog.interpreter import helper, term, error
from prolog.interpreter.signature import Signature
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# database

prefixsig = Signature.getsignature(":", 2)

def unpack_modname_and_predicate(rule):
    if helper.is_numeric(rule.argument_at(0)):
        error.throw_domain_error("atom", rule.argument_at(0))
    return rule.argument_at(0).name(), rule.argument_at(1)

@expose_builtin("abolish", unwrap_spec=["obj"], needs_module=True)
def impl_abolish(engine, heap, module, predicate):
    modname = None
    if predicate.signature().eq(prefixsig):
        modname, predicate = unpack_modname_and_predicate(predicate)
    name, arity = helper.unwrap_predicate_indicator(predicate)
    if arity < 0:
        error.throw_domain_error("not_less_than_zero", term.Number(arity))
    signature = Signature.getsignature(name, arity)
    if signature.get_extra("builtin"):
        error.throw_permission_error("modify", "static_procedure",
                                     predicate)
    if modname is not None:
        module = engine.modulewrapper.get_module(modname, predicate)
    try:
        del module.functions[signature]
    except KeyError:
        pass

@expose_builtin(["assert", "assertz"], unwrap_spec=["callable"],
        needs_module=True)
def impl_assert(engine, heap, module, rule):
    handle_assert(engine, heap, module, rule, True)

@expose_builtin("asserta", unwrap_spec=["callable"], needs_module=True)
def impl_asserta(engine, heap, module, rule):
    handle_assert(engine, heap, module, rule, False)

def handle_assert(engine, heap, module, rule, end):
    m = engine.modulewrapper
    current_modname = m.current_module.name
    engine.switch_module(module.name)
    if rule.signature().eq(prefixsig):
        modname, rule = unpack_modname_and_predicate(rule)
        engine.switch_module(modname)
    engine.add_rule(rule.getvalue(heap), end=end, old_modname=current_modname)

@expose_builtin("retract", unwrap_spec=["callable"], needs_module=True)
def impl_retract(engine, heap, module, pattern):
    modname = None
    if pattern.signature().eq(prefixsig):
        modname, pattern = unpack_modname_and_predicate(pattern)
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
    if modname is None:
        function = module.fetch_function(engine, head.signature())
    else:
        function = engine.modulewrapper.get_module(modname,
                pattern).fetch_function(engine, head.signature())
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



