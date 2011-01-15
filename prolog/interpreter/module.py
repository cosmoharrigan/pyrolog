import py

class Module(object):
    def __init__(self, name):
        self.name = name
        self.functions = {}
        self.exports = []
        self.uses = []
