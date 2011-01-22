import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Atom
from prolog.interpreter import error

@expose_builtin("module", unwrap_spec = ["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.add_module(name, exports)    

@expose_builtin("use_module", unwrap_spec = ["atom"])
def impl_use_module(engine, heap, modulename): 
    import os
    current_module = engine.current_module
    try:
        fd = os.open(modulename, os.O_RDONLY, 0777)
    except OSError, e:
        error.throw_existence_error("source_sink", modulename)
        assert 0, "unreachable" # make the flow space happy
    try:
        content = []
        while 1:
            s = os.read(fd, 4096)
            if not s:
                break
            content.append(s)
        file_content = "".join(content)
    finally:
        os.close(fd)
    engine.runstring(file_content)
    engine.set_current_module(current_module.name)
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
