import py, os
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.continuation import Heap, Engine
from prolog.interpreter import error
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true, prolog_raises
#from prolog.interpreter.test.isotests.fileutil import get_lines, get_files, deconstruct_list
from prolog.interpreter.error import UncaughtError

TESTDIR = str(py.path.local(__file__).dirpath().join('inriasuite'))

FAILURE = 'failure'
SUCCESS = 'success'

def deconstruct_line(line):
    HALT = 'halt,'
    FAIL = 'fail,'
    TRUE = 'true,'
    FLOAT = '0.33'
    ASSIGN = 'X ='
    CUT = '!,'
    line_0_5 = line[0:5]
    H_F_T = (HALT, FAIL, TRUE)
    
    if line_0_5 in H_F_T:
        if line_0_5 == FAIL:
            left = 'fail'
        elif line_0_5 == HALT:
            left = 'halt'
        elif line_0_5 == TRUE:
            left = 'true'
        right = line[6:]
    elif line.startswith(CUT):
        left = '!'
        right = line[3:]
    elif line.startswith(ASSIGN):
        left = 'X = "fred"'
        right = line[12:]
    elif line.startswith(FLOAT):
        left = '0.333 =:= 1/3'
        right = line[15:]
    else:
        first_open_par = line.find('(')
        brace_counter = 1
        i = first_open_par
        while brace_counter:
            i += 1
            if line[i] == '(':
                brace_counter += 1
            elif line[i] == ')':
                brace_counter -= 1
        left = line[0:i + 1]
        right = line[i + 2:].strip()
    return left, right
    

def get_lines(file_):
    testfile = open(TESTDIR + '/' + file_)
    for test in testfile.readlines():
        if test.endswith('%%SKIP%%\n') or test.find('0\'') != -1:
            continue
        if test.startswith('['):
            last_bracket = test.rfind(']')
            first_bracket = test.find('[') + 1
            relevant = test[first_bracket:last_bracket]
            left, right = deconstruct_line(relevant)
            yield left, right


def deconstruct_list(l):
    pieces = [piece for piece in l.split('], [')]
    pieces[0] = pieces[0][1:]
    return pieces


def get_files():
    _, _, content = os.walk(TESTDIR).next()
    for file in content:
        yield file


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
    try:
        prolog_raises(error, test)
    except UncaughtError, e:
        msg = repr(e.term)
        if 'existence_error' in msg:
            py.test.skip(msg)
        else:
            raise


def test_success_failure(test, mode):
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
        check = test + ', ' + goal.replace('<--', '=') + '.'
        assert_true(check)
