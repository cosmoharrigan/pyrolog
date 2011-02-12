from pypy.rlib.streamio import fdopen_as_stream
from prolog.interpreter.term import NonVar
from prolog.interpreter.error import UnificationFailed

class StreamWrapper(object):
    def __init__(self):
        # XXX use 0 and 1 instead of sys.stdin.fileno() and sys.stdout.fileno()
        # because otherwise problems at testing occur
        self.current_instream = PrologInputStream(fdopen_as_stream(0, "r", False))
        self.current_outstream = PrologOutputStream(fdopen_as_stream(1, "w", False))
        self.streams = {self.current_instream.fd(): self.current_instream,
                        self.current_outstream.fd(): self.current_outstream}
        self.aliases = {}

class PrologStream(NonVar):
    def __init__(self, stream):
        self.stream = stream
        self.alias = None

    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, PrologStream) and other.fd() == self.fd():
            return
        raise UnificationFailed

    def fd(self):   
        return self.stream.try_to_find_file_descriptor()

    def seek(self, offset, how):
        self.stream.seek(offset, how)

    def close(self):
        self.stream.close()

    def tell(self):
        return self.stream.tell()

class PrologInputStream(PrologStream):
    def __init__(self, stream):
        PrologStream.__init__(self, stream)

    def read(self, n):
        return self.stream.read(n)

class PrologOutputStream(PrologStream):
    def __init__(self, fd):
        PrologStream.__init__(self, fd)

    def write(self, data):
        self.stream.write(data)
