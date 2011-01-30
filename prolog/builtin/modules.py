import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Atom, Callable, Var, Term
from prolog.interpreter import error
from prolog.builtin.sourcehelper import get_source
from prolog.interpreter import continuation
from prolog.interpreter.helper import is_term

@expose_builtin("module", unwrap_spec=["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.add_module(name, exports)

@expose_builtin("use_module", unwrap_spec=["obj"], needs_module=True)
def impl_use_module(engine, heap, module, path):
    if is_term(path):
        if path.name() == "library":
            import os
            modulename = path.argument_at(0).name()
            for libpath, modules in engine.libs.iteritems():
                try:
                    modules[modulename]
                    path = Callable.build("%s/%s" % (libpath, modulename))
                    break
                except KeyError:
                    pass
    if isinstance(path, Atom):
        from os.path import basename
        path = path.name()
        modulename = basename(path)
        if path.endswith(".pl"):
            modulename = modulename[:len(modulename) - 3]
        if modulename not in engine.modules: # prevent recursive imports
            current_module = engine.current_module
            file_content = get_source(path)
            engine.runstring(file_content)
            module = engine.current_module = current_module
            # XXX should use name argument of module here like SWI
        imported_module = engine.modules[modulename]
        module.use_module(engine, imported_module)

@expose_builtin("module", unwrap_spec=["atom"])
def impl_module_1(engine, heap, name):
    engine.switch_module(name)

@expose_builtin(":", unwrap_spec=["atom", "callable"], 
        handles_continuation=True)
def impl_module_prefixing(engine, heap, modulename, 
        call, scont, fcont):
    try:
        module = engine.modules[modulename]
    except KeyError:
        error.throw_existence_error("procedure", call)
    return engine.call(call, module, scont, fcont, heap)

@expose_builtin("add_library_dir", unwrap_spec=["atom"])
def impl_add_library_dir(engine, heap, path):
    from os import listdir
    from os.path import basename, isdir, abspath, isabs
    if not isdir(path):
        error.throw_existence_error("source_sink", Callable.build(path))
    if isabs(path):
        basename = basename(path)
        abspath = path
    else:
        basename = path
        abspath = abspath(path)
    #engine.libs[basename] = abspath
    moduledict = {}
    modules = listdir(abspath)
    for module in modules:
        if module.endswith('.pl'):
            module = module[:len(module) - 3]
        moduledict[module] = True
    engine.libs[abspath] = moduledict

class LibraryDirContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, pathvar):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.pathvar = pathvar
        self.libkeys = engine.libs.keys()
        self.keycount = 0
        self.engine = engine

    def activate(self, fcont, heap):
        if self.keycount < len(self.libkeys):
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            from os.path import basename
            self.pathvar.unify(Callable.build(basename(
                    self.libkeys[self.keycount])), heap)
            self.keycount += 1
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()

@expose_builtin("library_directory", unwrap_spec=["obj"],
        handles_continuation=True)
def impl_library_directory(engine, heap, directory, scont, fcont):
    if isinstance(directory, Var):
        libcont = LibraryDirContinuation(engine, scont, fcont, heap, directory)
        return libcont, fcont, heap
    elif isinstance(directory, Atom):
        directory.unify(Callable.build(engine.libs[directory.name()]))
    else:
        error.UnificationFailed()
