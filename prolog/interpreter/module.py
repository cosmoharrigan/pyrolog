import py
from prolog.interpreter.signature import Signature

class Module(object):
    def __init__(self, name):
        self.name = name
        self.functions = {}
        self.exports = []

    def fetch_function(self, engine, signature):
        try:
            return self.functions[signature]
        except KeyError:
            return None

    def use_module(self, engine, module, imports=None):
        if imports is None:
            importlist = module.exports
        else:
            importlist = imports
        for sig in importlist:
            try:
                self.functions[sig] = module.functions[sig]
            except KeyError:
                pass
