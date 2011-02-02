from prolog.builtin.register import expose_builtin
from prolog.interpreter.continuation import Engine
from prolog.interpreter.heap import Heap
from prolog.interpreter import error
from prolog.interpreter import term
from pypy.rlib.streamio import fdopen_as_stream, open_file_as_stream
from prolog.interpreter.stream import PrologStream

rwa = {"read": "r", "write": "w", "append": "a"}

@expose_builtin("open", unwrap_spec=["atom", "atom", "obj"])
def impl_open(engine, heap, srcpath, mode, stream):
    if not isinstance(stream, term.Var):
        error.throw_type_error("variable", stream)
    try:
        stream = open_file_as_stream(srcpath, rwa[mode], False)
        engine.streams[stream.fd] = PrologStream(stream.fd)
    except KeyError:
        error.throw_domain_error("io_mode", term.Callable.build(mode))
    except OSError:
        error.throw_existence_error("source_sink", term.Callable.build(srcpath))
