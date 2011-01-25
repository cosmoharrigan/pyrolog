import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Atom
from prolog.interpreter import error
from prolog.builtin.sourcehelper import get_source

@expose_builtin("module", unwrap_spec = ["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.add_module(name, exports)    

@expose_builtin("use_module", unwrap_spec = ["atom"])
def impl_use_module(engine, heap, path):
    try:
        engine.modules[path] # prevent recursive imports
    except KeyError:
        current_module = engine.current_module
        file_content = get_source(path)
        engine.runstring(file_content)
        engine.set_current_module(current_module.name)
        # XXX should use name argument of module here like SWI
        from os.path import basename
        modulename = basename(path)
        if path.endswith(".pl"):
            modulename = modulename[:len(modulename) - 3]
        engine.current_module.use_module(engine, modulename)

@expose_builtin("module", unwrap_spec = ["atom"])
def impl_module_1(engine, heap, name):
    engine.set_current_module(name)   

@expose_builtin(":", unwrap_spec = ["atom", "callable"], 
        handles_continuation=True)
def impl_module_prefixing(engine, heap, modulename, 
        call, scont, fcont):
    try:
        module = engine.modules[modulename]
    except KeyError:
        error.throw_existence_error("procedure", call)
    return engine.call(call, module, scont, fcont, heap)
