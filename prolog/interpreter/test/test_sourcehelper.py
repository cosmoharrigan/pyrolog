import py
from prolog.builtin.sourcehelper import get_source
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true
from prolog.interpreter.test.tool import prolog_raises, create_file, delete_file
from prolog.interpreter.error import CatchableError

def test_get_source():
    content = "some important content"
    name = "__testfile__"
    f = create_file(name, content)
    source = get_source(name)
    assert source == content
    delete_file(name)

def test_source_does_not_exist():
    py.test.raises(CatchableError, "get_source('this_file_does_not_exist')")
