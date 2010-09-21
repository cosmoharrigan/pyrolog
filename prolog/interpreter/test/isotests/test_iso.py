import py
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.continuation import Heap, Engine
from prolog.interpreter import error
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true, prolog_raises
from prolog.interpreter.test.isotests.fileutil import get_lines, get_files, deconstruct_list

FAILURE = 'failure'
SUCCESS = 'success'

def pytest_generate_tests(metafunc):
    names = metafunc.funcargnames
    for f in get_files():
        for left, right in get_lines(f):
            # simple test: failure or success
            if right in (FAILURE, SUCCESS):
                if 'mode' in names:
                    metafunc.addcall(funcargs = dict(test = (left + '.'), mode = right))
            # test whether an error occurs
            if right.find('error') != -1:
                if 'error' in names:
                    metafunc.addcall(funcargs = dict(test = left, error = right))
            # test unification with a list of unifications
            if right.find('[') != -1 and right.find('error') == -1:
                lists = deconstruct_list(right[1:-2])
                if 'lists' in names:
                    metafunc.addcall(funcargs = dict(test = left, lists = lists))
        

def test_error(test, error):
    prolog_raises(error, test)


def test_success_failure(test, mode):
    print test
    try:
        if mode == FAILURE:
            assert_false(test)
        elif mode == SUCCESS:
            assert_true(test)
    except (error.UncaughtError, error.CatchableError), e:
        msg = repr(e.term)
        if 'existence_error' in msg:
            py.test.skip(msg)
        else:
            raise


def test_multiple_lists(test, lists):
    for goal in lists:
        assert_true(test + ', ' + goal.replace('<--', '=') + '.')


