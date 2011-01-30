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

    def use_module(self, engine, module):
        for sig in module.exports:
            self.functions[sig] = module.functions[sig]
