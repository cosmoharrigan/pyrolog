import py
from prolog.interpreter.signature import Signature

class Module(object):
    def __init__(self, name):
        self.name = name
        self.functions = {}
        self.exports = []
        self.uses = []

    def fetch_function(self, signature):
        sig = Signature.getsignature(signature.name, signature.numargs)
        try:
            return self.functions[sig]
        except KeyError:
            return None
