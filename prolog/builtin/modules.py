import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Atom, Callable, Var, Term, Number
from prolog.interpreter import error
from prolog.builtin.sourcehelper import get_source
from prolog.interpreter import continuation
from prolog.interpreter.helper import is_term, unwrap_predicate_indicator
from prolog.interpreter.signature import Signature

meta_args = "0123456789:?+-"
libsig = Signature.getsignature("library", 1)

@expose_builtin("module", unwrap_spec=["atom", "list"])
def impl_module(engine, heap, name, exports):
    engine.add_module(name, exports)

def handle_use_module(engine, heap, module, path, imports=None):
    if is_term(path):
        if path.signature().eq(libsig):
            arg = path.argument_at(0)
            path = None
            if isinstance(arg, Var):
                error.throw_instantiation_error()
            modulename = arg.name()
            for libpath, modules in engine.modulewrapper.libs.iteritems():
                try:
                    modules[modulename]
                except KeyError:
                    continue
                path = Callable.build("%s/%s" % (libpath, modulename))
                break
            if not path:
                error.throw_existence_error("source_sink", arg)

    if isinstance(path, Atom):
        m = engine.modulewrapper
        path = path.name()
        modulename = _basename(path)
        if path.endswith(".pl"):
            stop = len(modulename) - 3
            assert stop >= 0
            modulename = modulename[:stop]
        if modulename not in m.modules: # prevent recursive imports
            current_module = m.current_module
            file_content = get_source(path)
            engine.runstring(file_content)
            for sig in m.current_module.exports:
                if sig not in m.current_module.functions:
                    del m.modules[modulename]
                    m.current_module = current_module
                    error.throw_import_error(modulename, sig)
            module = m.current_module = current_module
            # XXX should use name argument of module here like SWI
        imported_module = m.modules[modulename]
        module.use_module(engine, heap, imported_module, imports)

@expose_builtin("use_module", unwrap_spec=["obj"], needs_module=True)
def impl_use_module(engine, heap, module, path):
    handle_use_module(engine, heap, module, path)

@expose_builtin("use_module", unwrap_spec=["obj", "list"], needs_module=True)
def impl_use_module_with_importlist(engine, heap, module, path, imports):
    importlist = []
    for sigatom in imports:
        importlist.append(Signature.getsignature(
                *unwrap_predicate_indicator(sigatom)))
    handle_use_module(engine, heap, module, path, importlist)

@expose_builtin("module", unwrap_spec=["atom"])
def impl_module_1(engine, heap, name):
    engine.switch_module(name)

@expose_builtin(":", unwrap_spec=["atom", "callable"], 
        handles_continuation=True)
def impl_module_prefixing(engine, heap, modulename, 
        call, scont, fcont):
    module = engine.modulewrapper.get_module(modulename, call)
    return engine.call(call, module, scont, fcont, heap)

@expose_builtin("add_library_dir", unwrap_spec=["atom"])
def impl_add_library_dir(engine, heap, path):
    from os import listdir
    from os.path import isdir, abspath, isabs
    if not isdir(path):
        error.throw_existence_error("source_sink", Callable.build(path))
    if isabs(path):
        basename = _basename(path)
        abspath = path
    else:
        basename = path
        abspath = abspath(path)
    moduledict = {}
    modules = listdir(abspath)
    for module in modules:
        if module.endswith('.pl'):
            stop = len(module) - 3
            assert stop >= 0
            module = module[:stop]
        moduledict[module] = True
    engine.modulewrapper.libs[abspath] = moduledict

class LibraryDirContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, pathvar):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.pathvar = pathvar
        self.libkeys = engine.modulewrapper.libs.keys()
        self.keycount = 0
        self.engine = engine

    def activate(self, fcont, heap):
        if self.keycount < len(self.libkeys):
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.pathvar.unify(Callable.build(_basename(
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
        for key in engine.modulewrapper.libs.keys():
            if _basename(key) == directory.name():
                return scont, fcont, heap
    raise error.UnificationFailed()

@expose_builtin("this_module", unwrap_spec=["obj"])
def impl_this_module(engine, heap, module):
    name = engine.modulewrapper.current_module.name
    Callable.build(name).unify(module, heap)  

@expose_builtin("meta_predicate", unwrap_spec=["obj"])
def impl_meta_predicate(engine, heap, predlist):
    while predlist:
        if isinstance(predlist, Var):
            error.throw_instantiation_error()
        if predlist.name() == ",":
            pred = predlist.argument_at(0)
            predlist = predlist.argument_at(1)
        else:
            pred = predlist
            predlist = None
        args = unwrap_meta_arguments(pred)
        engine.modulewrapper.current_module.add_meta_predicate(
                pred.signature(), args)
          
def unwrap_meta_arguments(predicate):
    args = predicate.arguments()
    arglist = []
    for arg in args:
        if isinstance(arg, Var):
            error.throw_instantiation_error()
        elif isinstance(arg, Atom) and arg.name() in meta_args:
            val = arg.name()
            arglist.append(val)
        elif isinstance(arg, Number) and 0 <= arg.num <= 9:
            val = str(arg.num)
            arglist.append(val)
        else:
            error.throw_domain_error("expected one of 0..9, :, ?, +, -", arg)
    return arglist

class CurrentModuleContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, modvar):
        continuation.ChoiceContinuation.__init__(self, engine, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.modvar = modvar
        self.engine = engine
        self.modcount = 0
        self.mods = self.engine.modulewrapper.modules.keys()
        self.nummods = len(self.mods)

    def activate(self, fcont, heap):
        if self.modcount < self.nummods:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            self.modvar.unify(Callable.build(self.mods[self.modcount]), heap)
            self.modcount += 1
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()

@expose_builtin("current_module", unwrap_spec=["obj"],
        handles_continuation=True)
def impl_current_module(engine, heap, module, scont, fcont):
    if isinstance(module, Atom):
        try:
            engine.modulewrapper.modules[module.name()]
        except KeyError:
            raise error.UnificationFailed()
    elif isinstance(module, Var):
        scont = CurrentModuleContinuation(engine, scont, fcont, heap, module)
    else:
        raise error.UnificationFailed()
    return scont, fcont, heap

def _basename(path):
    index = path.rfind("/") + 1 # XXX OS specific
    if index == 0:
        return path
    assert index >= 0
    return path[index:]
