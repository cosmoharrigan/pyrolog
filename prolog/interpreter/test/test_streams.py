import py
from prolog.interpreter.continuation import Engine
from prolog.interpreter.parsing import get_engine
from prolog.interpreter.stream import PrologInputStream , PrologOutputStream
from prolog.interpreter.test.tool import create_file, delete_file, \
prolog_raises, assert_true

def test_current_stream_after_startup():
    e = get_engine("")
    assert isinstance(e.current_instream, PrologInputStream)
    assert isinstance(e.current_outstream, PrologOutputStream)
    assert e.current_instream.fd == 0
    assert e.current_outstream.fd == 1

def test_open():
    src = "__src__"
    create_file(src, "")

    try:
        e = Engine()
        assert_true("open('%s', read, X)." % src, e)
        assert len(e.streams) == 3

        prolog_raises("existence_error(X, Y)", "open('does_not_exist', read, X)")
        prolog_raises("type_error(X, Y)", "open('%s', read, a)" % src)
        assert_true("open('%s', write, X)." % src)
        assert_true("open('%s', append, X)." % src)
        prolog_raises("domain_error(X, Y)", "open('%s', asdsadsad, X)")
    finally:
        delete_file(src)

