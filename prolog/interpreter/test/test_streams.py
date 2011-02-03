# coding=utf-8

import py
from prolog.interpreter.continuation import Engine
from prolog.interpreter.parsing import get_engine
from prolog.interpreter.stream import PrologInputStream , PrologOutputStream
from prolog.interpreter.test.tool import create_file, delete_file, \
prolog_raises, assert_true, assert_false, file_content

def test_current_stream_after_startup():
    e = get_engine("")
    assert isinstance(e.streamwrapper.current_instream, PrologInputStream)
    assert isinstance(e.streamwrapper.current_outstream, PrologOutputStream)
    assert e.streamwrapper.current_instream.fd() == 0
    assert e.streamwrapper.current_outstream.fd() == 1

def test_open():
    src = "__src__"
    create_file(src, "")

    try:
        e = Engine()
        assert_true("open('%s', read, S)." % src, e)
        assert len(e.streamwrapper.streams) == 3

        prolog_raises("existence_error(X, Y)", "open('does_not_exist', read, S)")
        prolog_raises("type_error(X, Y)", "open('%s', read, a)" % src)
        assert_true("open('%s', write, S)." % src)
        assert_true("open('%s', append, S)." % src)
        prolog_raises("domain_error(X, Y)", "open('%s', asdsadsad, X)")
    finally:
        delete_file(src)

def test_close():
    src = "__src__"
    create_file(src, "")

    try:
        e = get_engine("""
        :- open('%s', read, S), close(S).
        """ % src)
        assert len(e.streamwrapper.streams) == 2
        assert 0 in e.streamwrapper.streams
        assert 1 in e.streamwrapper.streams
        prolog_raises("instantiation_error", "close(X)")
        prolog_raises("domain_error(stream, Y)", "close(a)")
    finally:
        delete_file(src)

def test_get_char():
    src = "__src__"
    create_file(src, "aü½")
    try:
        assert_true("""
        open('%s', read, S),
        get_char(S, C), C = 'a',
        get_char(S, D), D = 'ü', 
        get_char(S, E), E = '½', 
        close(S).
        """ % src)
        assert_false("""
        open('%s', read, S), 
        get_char(S, some_atom).
        """ % src)
    finally:
        delete_file(src)

def test_get_char_at_eof():
    src = "__empty__"
    create_file(src, "")
    try:
        assert_true("""
        open('%s', read, S),
        get_char(S, C), C = end_of_file,
        close(S).
        """ % src)
    finally:
        delete_file(src)

def test_get_byte():
    src = "__src__"
    create_file(src, "\xa4\x17\xcf")
    try:
        assert_true("""
        open('%s', read, S),
        get_byte(S, B), B = 164,
        get_byte(S, C), C = 23,
        get_byte(S, D), D = 207,
        get_byte(S, E), E = -1,
        close(S).
        """ % src)
    finally:
        delete_file(src)

def test_get_code():
    src = "__src__"
    create_file(src, "a1¼")
    try:
        assert_true("""
        open('%s', read, S),
        get_code(S, B), B = 97,
        get_code(S, C), C = 49,
        get_code(S, D), D = 194,
        get_code(S, E), E = 188,
        get_code(S, F), F = -1,
        close(S).
        """ % src)
    finally:
        delete_file(src)

def test_at_end_of_stream_1():
    src = "__src__"
    create_file(src, "abc")
    try:
        assert_true("""
        open('%s', read, S),
        get_byte(S, B1),
        get_byte(S, B2),
        get_byte(S, B3),
        at_end_of_stream(S),
        close(S).
        """ % src)
        assert_false("""
        open('%s', read, S),
        get_byte(S, B1),
        get_byte(S, B2),
        at_end_of_stream(S).
        """ % src)
    finally:
        delete_file(src)

def XXX_test_at_end_of_stream_or():
    src = "__src__"
    create_file(src, "a")
    try:
        assert_false("""
        open('%s', read, S),
        (at_end_of_stream(S); at_end_of_stream(S)).
        """ % src)
    finally:
        delete_file(src)

def test_at_end_of_stream_empty():
    src = "__src__"
    create_file(src, "")
    try:
        assert_true("""
        open('%s', read, S),
        at_end_of_stream(S),
        close(S).
        """ % src)
    finally:
        delete_file(src)

def test_peek_char():
    src = "__src__"
    empty = "__empty__"
    create_file(src, "aü¼")
    create_file(empty, "")
    try:
        assert_true("""
        open('%s', read, S),
        peek_char(S, C), C = 'a',
        peek_char(S, D), D = 'a',
        get_char(S, _),
        peek_char(S, E), E = 'ü',
        peek_char(S, F), F = 'ü',
        get_char(S, _),
        peek_char(S, G), G = '¼',
        get_char(S, _),
        peek_char(S, Z), Z = end_of_file,
        close(S).
        """ % src)

        assert_true("""
        open('%s', read, S),
        peek_char(S, end_of_file),
        close(S).
        """ % empty)
    finally:
        delete_file(src)
        delete_file(empty)

def test_peek_byte():
    src = "__src__"
    empty = "__empty__"
    create_file(src, "\x94\xef")
    create_file(empty, "")
    try:
        assert_true("""
        open('%s', read, S),
        peek_byte(S, C), C = 148,
        peek_byte(S, D), D = 148,
        get_byte(S, _),
        peek_byte(S, E), E = 239,
        peek_byte(S, F), F = 239,
        get_byte(S, _),
        peek_byte(S, Z), Z = -1,
        close(S).
        """ % src)

        assert_true("""
        open('%s', read, S),
        peek_byte(S, -1),
        close(S).
        """ % empty)
    finally:
        delete_file(src)
        delete_file(empty)

def test_peek_code():
    src = "__src__"
    empty = "__empty__"
    create_file(src, "¼")
    create_file(empty, "")
    try:
        assert_true("""
        open('%s', read, S),
        peek_code(S, C), C = 194,
        peek_code(S, D), D = 194,
        get_code(S, _),
        peek_code(S, E), E = 188,
        get_code(S, _),
        peek_code(S, F), F = -1,
        close(S).
        """ % src)

        assert_true("""
        open('%s', read, S),
        peek_code(S, -1),
        close(S).
        """ % empty)
    finally:
        delete_file(src)
        delete_file(empty)

def test_put_char():
    src = "__src__"
    target = "__target__"
    content = "aö½"
    create_file(src, content)
    create_file(target, "")
    try:
        assert_true("""
        open('%s', read, R), open('%s', write, W),
        get_char(R, C1), put_char(W, C1),
        get_char(R, C2), put_char(W, C2),
        get_char(R, C3), put_char(W, C3),
        close(R), close(W).
        """ % (src, target))
        assert content == file_content(src)
    finally:
        delete_file(src)
        delete_file(target)

def test_put_char_type_error():
    src = "__src__"
    create_file(src, "") 
    try:
        prolog_raises("type_error(X, Y)", """
        open('%s', write, S),
        put_char(S, aa)
        """ % src)
    finally:
        delete_file(src)
