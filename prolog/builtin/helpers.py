def unpack_modname_and_predicate(rule):
    return rule.argument_at(0).name(), rule.argument_at(1)
