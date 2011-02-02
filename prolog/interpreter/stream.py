from pypy.rlib.streamio import fdopen_as_stream
from prolog.interpreter.term import NonVar
from prolog.interpreter.error import UnificationFailed

class PrologStream(NonVar):
    def __init__(self, stream):
        self.stream = stream

    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, PrologStream) and other.fd == self.fd:
            return
        raise UnificationFailed

    def fd(self):   
        return self.stream.fd

    def close(self):
        self.stream.close()

class PrologInputStream(PrologStream):
    def __init__(self, stream):
        PrologStream.__init__(self, stream)

    def read(self, n):
        return self.stream.read(n)

class PrologOutputStream(PrologStream):
    def __init__(self, fd):
        PrologStream.__init__(self, fd)
