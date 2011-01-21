import py
from prolog.builtin.register import expose_builtin


@expose_builtin("module", unwrap_spec = ["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.add_module(name, exports)    

@expose_builtin("use_module", unwrap_spec = ["atom"])
def impl_use_module(engine, heap, modulename):
    engine.current_module.use_module(engine, modulename)

@expose_builtin("module", unwrap_spec = ["atom"])
def impl_module_1(engine, heap, name):
    engine.set_current_module(name)   

@expose_builtin(":", unwrap_spec = ["atom", "callable"], 
        handles_continuation=True)
def impl_module_prefixing(engine, heap, modulename, 
        call, scont, fcont):
    module = engine.modules[modulename]
    return engine.call(call, module, scont, fcont, heap)
