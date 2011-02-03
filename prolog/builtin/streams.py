from prolog.builtin.register import expose_builtin
from prolog.interpreter.continuation import Engine
from prolog.interpreter.heap import Heap
from prolog.interpreter import error
from prolog.interpreter import term
from pypy.rlib.streamio import fdopen_as_stream, open_file_as_stream
from prolog.interpreter.stream import PrologStream, PrologInputStream, \
PrologOutputStream
from prolog.interpreter import helper
import os

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
        engine.streamwrapper.streams[prolog_stream.fd()] = prolog_stream
        stream.unify(prolog_stream, heap)
    except KeyError:
        error.throw_domain_error("io_mode", term.Callable.build(mode))
    except OSError:
        error.throw_existence_error("source_sink", term.Callable.build(srcpath))

@expose_builtin("close", unwrap_spec=["stream"])
def impl_close(engine, heap, stream):
    engine.streamwrapper.streams.pop(stream.fd()).close()

def read_unicode_char(stream):
    c = stream.read(1)
    bytes_read = 1
    if c == "":
        return "end_of_file", 0
    if ord(c) > 127: # beyond ASCII, so a character consists of 2 bytes
        c += stream.read(1)
        bytes_read += 1
    return c, bytes_read

def peek_unicode_char(stream):
    c, num = read_unicode_char(stream)
    if num > 0:
        try:
            stream.seek(-num, os.SEEK_CUR)
        except OSError:
            pass
    return c

def peek_byte(stream):
    byte = stream.read(1)
    if byte != '':
        try:
            stream.seek(-1, os.SEEK_CUR)
        except OSError:
            pass
        return ord(byte)
    return -1

@expose_builtin("get_char", unwrap_spec=["stream", "obj"])
def impl_get_char(engine, heap, stream, obj):
    if isinstance(stream, PrologInputStream):
        char, _ = read_unicode_char(stream)
        obj.unify(term.Callable.build(char), heap)

@expose_builtin("get_byte", unwrap_spec=["stream", "obj"])
def impl_get_byte(engine, heap, stream, obj):
    if isinstance(stream, PrologInputStream):
        byte = stream.read(1)
        if byte != '':
            code = ord(byte)
        else:
            code = -1
        obj.unify(term.Number(code), heap)

@expose_builtin("get_code", unwrap_spec=["stream", "obj"])
def impl_get_code(engine, heap, stream, obj):
    impl_get_byte(engine, heap, stream, obj)

@expose_builtin("at_end_of_stream", unwrap_spec=["stream"])
def impl_at_end_of_stream(engine, heap, stream):
    byte = peek_byte(stream)
    if byte > -1:
        raise error.UnificationFailed()

@expose_builtin("peek_char", unwrap_spec=["stream", "obj"])
def impl_peek_char(engine, heap, stream, obj):
    char = peek_unicode_char(stream)
    obj.unify(term.Callable.build(char), heap)

@expose_builtin("peek_byte", unwrap_spec=["stream", "obj"])
def impl_peek_byte(engine, heap, stream, obj):
    byte = peek_byte(stream)
    obj.unify(term.Number(byte), heap)

@expose_builtin("peek_code", unwrap_spec=["stream", "obj"])
def impl_peek_code(engine, heap, stream, obj):
    impl_peek_byte(engine, heap, stream, obj)
