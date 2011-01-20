import py
from prolog.interpreter.signature import Signature

class Module(object):
    def __init__(self, name):
        self.name = name
        self.functions = {}
        self.exports = []

    def fetch_function(self, signature):
        sig = Signature.getsignature(signature.name, signature.numargs)
        try:
            return self.functions[sig]
        except KeyError:
            return None

    def use_module(self, engine, modulename):
        module = engine.modules[modulename]
        for sig in module.exports:
            keysig = Signature.getsignature(sig.name, sig.numargs)
            self.functions[keysig] = module.functions[keysig]
