from prolog.builtin.register import expose_builtin
from prolog.interpreter.continuation import Engine
from prolog.interpreter.heap import Heap
from prolog.interpreter import error
from prolog.interpreter import term
from pypy.rlib.streamio import fdopen_as_stream, open_file_as_stream
from prolog.interpreter.stream import PrologStream, PrologInputStream, \
PrologOutputStream
from prolog.interpreter import helper

rwa = {"read": "r", "write": "w", "append": "a"}

@expose_builtin("open", unwrap_spec=["atom", "atom", "obj"])
def impl_open(engine, heap, srcpath, mode, stream):
    if not isinstance(stream, term.Var):
        error.throw_type_error("variable", stream)
    try:
        mode = rwa[mode]
        if mode == "r":
            cls = PrologInputStream
        else:
            cls = PrologOutputStream
        prolog_stream = cls(open_file_as_stream(srcpath, mode, False))
        engine.streamwrapper.streams[prolog_stream.fd] = prolog_stream
        stream.unify(prolog_stream, heap)
    except KeyError:
        error.throw_domain_error("io_mode", term.Callable.build(mode))
    except OSError:
        error.throw_existence_error("source_sink", term.Callable.build(srcpath))

@expose_builtin("close", unwrap_spec=["stream"])
def impl_close(engine, heap, stream):
    engine.streamwrapper.streams.pop(stream).close()

def read_unicode_char(stream):
    c = stream.read(1)
    if c == "":
        return "end_of_file"
    if ord(c) > 127: # beyond ASCII, so a character consists of 2 bytes
        c += stream.read(1)
    return c

@expose_builtin("get_char", unwrap_spec=["stream", "obj"])
def impl_get_char(engine, heap, fd, obj):
    stream = engine.streamwrapper.streams[fd]
    if isinstance(stream, PrologInputStream):
        char = read_unicode_char(stream)
        obj.unify(term.Callable.build(char), heap)
