import py
from pypy.rlib import jit
from prolog.interpreter.signature import Signature
from prolog.interpreter import error
from prolog.interpreter.term import Callable, Atom
from prolog.interpreter.function import Function

class ModuleWrapper(object):
    def __init__(self, engine):
        self.engine = engine
        self.user_module = Module("user")
        self.modules = {"user": self.user_module} # all known modules
        self.current_module = self.user_module
        self.libs = {}
        self.system = None

    def init_system_module(self):
        from prolog.builtin.sourcehelper import get_source
        source = get_source("system.pl")
        self.engine.runstring(source)
        self.system = self.modules["system"]
        self.current_module = self.user_module

    def get_module(self, name, errorterm):
        try:
            return self.modules[name]
        except KeyError:
            assert isinstance(errorterm, Callable)
            error.throw_existence_error("procedure",
                errorterm.get_prolog_signature())
        

class Module(object):
    def __init__(self, name):
        self.name = name
        self.nameatom = Atom(name)
        self.functions = {}
        self.exports = []

    def fetch_function(self, signature):
        try:
            return self.functions[signature]
        except KeyError:
            return None

    def add_meta_predicate(self, signature, arglist):
        func = self.lookup(signature)
        func.meta_args = arglist

    @jit.purefunction_promote("0")
    def lookup(self, signature):
        try:
            function = self.functions[signature]
        except KeyError:
            function = Function()
            self.functions[signature] = function
        return function

    def use_module(self, engine, heap, module, imports=None):
        if imports is None:
            importlist = module.exports
        else:
            importlist = imports
        for sig in importlist:
            try:
                self.functions[sig] = module.functions[sig]
            except KeyError:
                pass

    def __repr__(self):
        return "Module('%s')" % self.name
        
