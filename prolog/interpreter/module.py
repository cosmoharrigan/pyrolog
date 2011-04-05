import py
from prolog.interpreter.signature import Signature
from prolog.interpreter import error
from prolog.interpreter.term import Callable, Atom

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
            error.throw_existence_error("procedure",
                errorterm.get_prolog_signature())
        

class Module(object):
    def __init__(self, name):
        self.name = name
        self.functions = {}
        self.exports = []
        self.meta_predicates = {}

    def fetch_function(self, engine, signature):
        try:
            return self.functions[signature]
        except KeyError:
            return None

    def add_meta_predicate(self, signature, indexlist):
        self.meta_predicates[signature] = indexlist

    def use_module(self, engine, module, imports=None):
        if imports is None:
            importlist = module.exports
        else:
            importlist = imports
        #import pdb; pdb.set_trace()
        for sig in importlist:
            try:
                #self.functions[sig] = module.functions[sig]
                func = module.functions[sig]
                import pdb; pdb.set_trace()
                if sig in module.meta_predicates:
                    metaargs = module.meta_predicates[sig]
                    for i in range(len(metaargs)):
                        arg = metaargs[i]
                        if arg in "?+-":
                            continue
                        # simple case: test(X)
                        if func.rulechain.headargs[i].name() != ':':
                            term = func.rulechain.headargs[i]
                            newterm = Callable.build(':', [Atom(self.name), term])
                            func.rulechain.headargs[i] = newterm
                        # complex case: text(module:X)
                self.functions[sig] = func
            except KeyError:
                pass
