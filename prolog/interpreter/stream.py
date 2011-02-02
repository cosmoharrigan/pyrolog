from pypy.rlib.streamio import fdopen_as_stream
from prolog.interpreter.term import NonVar
from prolog.interpreter.error import UnificationFailed

class PrologStream(NonVar):
    def __init__(self, fd):
        assert isinstance(fd, int)
        self.fd = fd

    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, PrologStream) and other.fd == self.fd:
            return
        raise UnificationFailed

class PrologInputStream(PrologStream):
    def __init__(self, fd):
        PrologStream.__init__(self, fd)
        self.stream = fdopen_as_stream(fd, 'r', False)

class PrologOutputStream(PrologStream):
    def __init__(self, fd):
        PrologStream.__init__(self, fd)
        self.stream = fdopen_as_stream(fd, 'w', False)
