import py
from prolog.builtin.register import expose_builtin


@expose_builtin("module", unwrap_spec = ["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.set_currently_parsed_module(name, exports)    


@expose_builtin("use_module", unwrap_spec = ["atom"])
def impl_use_module(engine, heap, module):
    pass
