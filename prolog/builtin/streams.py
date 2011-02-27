import os
from prolog.builtin.register import expose_builtin
from prolog.interpreter.continuation import Engine
from prolog.interpreter.heap import Heap
from prolog.interpreter import error
from prolog.interpreter import term
from pypy.rlib.streamio import fdopen_as_stream, open_file_as_stream
from prolog.interpreter.stream import PrologStream, PrologInputStream, \
PrologOutputStream
from prolog.interpreter import helper
from prolog.builtin.formatting import TermFormatter

rwa = {"read": "r", "write": "w", "append": "a"}
seek_mode = {"bof": os.SEEK_SET, "current": os.SEEK_CUR, "eof": os.SEEK_END}

def make_option_dict(options):
    opts = {}
    for option in options:
        opts[option.name()] = option.argument_at(0).name()
    return opts

@expose_builtin("open", unwrap_spec=["atom", "atom", "obj", "list"])
def impl_open_options(engine, heap, srcpath, mode, stream, options):
    if not isinstance(stream, term.Var):
        error.throw_type_error("variable", stream)
    opts = make_option_dict(options)
    try:
        mode = rwa[mode]
        if mode == "r":
            cls = PrologInputStream
        else:
            cls = PrologOutputStream

        try:
            buffering = opts["buffer"]
            if buffering == "full":
                buffering = -1
            elif buffering == "line":
                buffering == 1
            elif buffering == "false":
                buffering = 0
            else:
                buffering = -1
        except KeyError:
            buffering = -1

        prolog_stream = cls(open_file_as_stream(srcpath, mode, buffering))
        engine.streamwrapper.streams[prolog_stream.fd()] = prolog_stream

        try:
            alias = opts["alias"]
            prolog_stream.alias = alias
        except KeyError:
            alias = "$stream_%d" % prolog_stream.fd()
        engine.streamwrapper.aliases[alias] = prolog_stream
        stream.unify(term.Callable.build(alias), heap)
    except KeyError:
        error.throw_domain_error("io_mode", term.Callable.build(mode))
    except OSError:
        error.throw_existence_error("source_sink", term.Callable.build(srcpath))

@expose_builtin("open", unwrap_spec=["atom", "atom", "obj"])
def impl_open(engine, heap, srcpath, mode, stream):
    impl_open_options(engine, heap, srcpath, mode, stream, [])

@expose_builtin("close", unwrap_spec=["stream"])
def impl_close(engine, heap, stream):
    if stream.fd() not in [0, 1]:
        w = engine.streamwrapper
        w.streams.pop(stream.fd()).close()
        try:
            if w.aliases[stream.alias].fd() == w.current_instream.fd():
                w.current_instream = w.streams[0]
            if w.aliases[stream.alias].fd() == w.current_outstream.fd():
                w.current_outstream = w.streams[1]
            w.aliases.pop(stream.alias)
        except KeyError:
            pass

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

def read_term(stream):
    singles = 0
    doubles = 0
    chars = []
    dot = False
    while not dot:
        char, _ = read_unicode_char(stream)
        if char == "end_of_file":
            break

    return "".join(chars)

def validate_stream_mode(stream, mode): 
    if isinstance(stream, PrologInputStream) and mode == "write":
        error.throw_permission_error("output", "stream", term.Atom(stream.alias))
    if isinstance(stream, PrologOutputStream) and mode == "read":
        error.throw_permission_error("input", "stream", term.Atom(stream.alias))

@expose_builtin("get_char", unwrap_spec=["stream", "obj"])
def impl_get_char(engine, heap, stream, obj):
    validate_stream_mode(stream, "read")
    char, _ = read_unicode_char(stream)
    obj.unify(term.Callable.build(char), heap)

@expose_builtin("get_char", unwrap_spec=["obj"])
def impl_get_char_1(engine, heap, obj):
    impl_get_char(engine, heap, engine.streamwrapper.current_instream, obj)

@expose_builtin("get_byte", unwrap_spec=["stream", "obj"])
def impl_get_byte(engine, heap, stream, obj):
    validate_stream_mode(stream, "read")
    byte = stream.read(1)
    if byte != '':
        code = ord(byte)
    else:
        code = -1
    obj.unify(term.Number(code), heap)

@expose_builtin("get_byte", unwrap_spec=["obj"])
def impl_get_byte_1(engine, heap, obj):
    impl_get_byte(engine, heap, engine.streamwrapper.current_instream, obj)

@expose_builtin("get_code", unwrap_spec=["stream", "obj"])
def impl_get_code(engine, heap, stream, obj):
    impl_get_byte(engine, heap, stream, obj)

@expose_builtin("get_code", unwrap_spec=["obj"])
def impl_get_code_1(engine, heap, obj):
    impl_get_code(engine, heap, engine.streamwrapper.current_instream, obj)

@expose_builtin("at_end_of_stream", unwrap_spec=["stream"])
def impl_at_end_of_stream(engine, heap, stream):
    byte = peek_byte(stream)
    if byte > -1:
        raise error.UnificationFailed()

@expose_builtin("peek_char", unwrap_spec=["stream", "obj"])
def impl_peek_char(engine, heap, stream, obj):
    validate_stream_mode(stream, "read")
    char = peek_unicode_char(stream)
    obj.unify(term.Callable.build(char), heap)

@expose_builtin("peek_byte", unwrap_spec=["stream", "obj"])
def impl_peek_byte(engine, heap, stream, obj):
    validate_stream_mode(stream, "read")
    byte = peek_byte(stream)
    obj.unify(term.Number(byte), heap)

@expose_builtin("peek_code", unwrap_spec=["stream", "obj"])
def impl_peek_code(engine, heap, stream, obj):
    impl_peek_byte(engine, heap, stream, obj)

@expose_builtin("put_char", unwrap_spec=["stream", "atom"])
def impl_put_char(engine, heap, stream, atom):
    validate_stream_mode(stream, "write")
    length = len(atom)
    if length == 1:
        stream.write(atom)
        return
    elif length == 2:
        if ord(atom[0]) > 127: # not ASCII
            stream.write(atom)
            return
    error.throw_type_error("character", term.Callable.build(atom))

@expose_builtin("put_char", unwrap_spec=["atom"])
def impl_put_char_1(engine, heap, obj):
    impl_put_char(engine, heap, engine.streamwrapper.current_outstream, obj)

@expose_builtin("put_byte", unwrap_spec=["stream", "int"])
def impl_put_byte(engine, heap, stream, byte):
    validate_stream_mode(stream, "write")
    if byte < 0:
        # XXX have to care about bigints
        error.throw_type_error("byte", term.Number(byte))
    stream.write(chr(byte))

@expose_builtin("put_byte", unwrap_spec=["int"])
def impl_put_byte_1(engine, heap, obj):
    impl_put_byte(engine, heap, engine.streamwrapper.current_outstream, obj)

@expose_builtin("current_input", unwrap_spec=["obj"])
def impl_current_input(engine, heap, obj):
    if not isinstance(obj, term.Var) and not isinstance(obj, term.Atom):
        error.throw_domain_error("stream", obj)
    obj.unify(term.Atom(engine.streamwrapper.current_instream.alias), heap)

@expose_builtin("current_output", unwrap_spec=["obj"])
def impl_current_output(engine, heap, obj):
    if not isinstance(obj, term.Var) and not isinstance(obj, term.Atom):
        error.throw_domain_error("stream", obj)
    obj.unify(term.Atom(engine.streamwrapper.current_outstream.alias), heap)

@expose_builtin("set_input", unwrap_spec=["stream"])
def impl_set_input(engine, heap, stream):
    validate_stream_mode(stream, "read")
    engine.streamwrapper.current_instream = stream
    
@expose_builtin("set_output", unwrap_spec=["stream"])
def impl_set_output(engine, heap, stream):
    validate_stream_mode(stream, "write")
    engine.streamwrapper.current_outstream = stream

@expose_builtin("seek", unwrap_spec=["stream", "int", "atom", "obj"])
def impl_seek(engine, heap, stream, offset, mode, obj):
    try:
        mode = seek_mode[mode]
    except KeyError:
        error.throw_domain_error("seek_method", term.Callable.build(mode))
    try:
        stream.seek(offset, mode)
    except OSError:
        error.throw_domain_error("position", term.Number(offset))
    pos = int(stream.tell())
    obj.unify(term.Number(pos), heap)

@expose_builtin("nl", unwrap_spec=["stream"])
def impl_nl(engine, heap, stream):
    validate_stream_mode(stream, "write")
    stream.write("\n")

@expose_builtin("nl", unwrap_spec=[])
def impl_nl_0(engine, heap):
    impl_nl(engine, heap, engine.streamwrapper.current_outstream)

@expose_builtin("write", unwrap_spec=["stream", "concrete"])
def impl_write(engine, heap, stream, term):
    validate_stream_mode(stream, "write")
    formatter = TermFormatter.from_option_list(engine, [])
    stream.write(formatter.format(term))

@expose_builtin("write", unwrap_spec=["concrete"])
def impl_write_1(engine, heap, term):
    impl_write(engine, heap, engine.streamwrapper.current_outstream, term)

@expose_builtin("write_term", unwrap_spec=["stream", "concrete", "list"])
def impl_write_term(engine, heap, stream, term, options):
    validate_stream_mode(stream, "write")
    formatter = TermFormatter.from_option_list(engine, options)
    stream.write(formatter.format(term))
 
@expose_builtin("write_term", unwrap_spec=["concrete", "list"])
def impl_write_term_2(engine, heap, term, options):
    impl_write_term(engine, heap, engine.streamwrapper.current_outstream,
            term, options)

def read_till_next_dot(stream):
    charlist = []
    tlist = ["%", "", "end_of_file"]
    whitespace = True
    ignore = False
    while True:
        char, _ = read_unicode_char(stream)
        if char == "%":
            ignore = True
        if char == "\n":
            ignore = False
            continue
        if char == "end_of_file":
            ignore = False
        if char.strip() == "":
            continue
        if not ignore:
            if char == "end_of_file":
                if whitespace:
                    return "end_of_file."
                else:
                    error.throw_syntax_error("Unexpected end of file")
            else:
                whitespace = False
            charlist.append(char)
            if char == ".":
                nextchar, n = read_unicode_char(stream)
                stream.seek(-n, 1)
                if nextchar.strip() in tlist:
                    return "".join(charlist)

@expose_builtin("read", unwrap_spec=["stream", "obj"])
def impl_read(engine, heap, stream, obj):
    from prolog.interpreter.parsing import parse_query_term
    validate_stream_mode(stream, "read")
    src = read_till_next_dot(stream)
    parsed = parse_query_term(src)
    obj.unify(parsed, heap)

@expose_builtin("read", unwrap_spec=["obj"])
def impl_read_1(engine, heap, obj):
    impl_read(engine, heap, engine.streamwrapper.current_instream, obj)

@expose_builtin("see", unwrap_spec=["atom"])
def impl_see(engine, heap, obj):
    w = engine.streamwrapper
    try:
        stream = w.aliases[obj]
        impl_set_input(engine, heap, stream)
    except KeyError:
        try:
            stream = PrologInputStream(open_file_as_stream(obj,
                    rwa["read"], -1))
            w.streams[stream.fd()] = stream
            w.aliases["$stream_%d" % stream.fd()] = stream
            impl_set_input(engine, heap, stream)
        except OSError:
            error.throw_existence_error("source_sink",
                    term.Callable.build(obj))

@expose_builtin("seen")
def impl_seen(engine, heap):
    impl_close(engine, heap, engine.streamwrapper.current_instream)
