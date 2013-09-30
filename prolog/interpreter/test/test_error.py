import py, pytest

from prolog.interpreter.parsing import get_engine
from prolog.interpreter.parsing import get_query_and_vars
from prolog.interpreter.error import UncaughtError
from prolog.interpreter.signature import Signature

def get_uncaught_error(query, e):
    if isinstance(query, str):
        (query, _) = get_query_and_vars(query)
    return pytest.raises(UncaughtError, e.run_query_in_current, query).value


def test_errstr():
    e = get_engine("""
        f(X) :- drumandbass(X).
    """)
    error = get_uncaught_error("f(X).", e)
    assert error.get_errstr(e) == "Undefined procedure: drumandbass/1"

def test_exception_knows_rule():
    e = get_engine("""
        f(1).
        f(X) :- drumandbass(X).
    """)
    (t, vs) = get_query_and_vars("f(X), X = 2.")

    m = e.modulewrapper
    sig = t.argument_at(0).signature()
    rule = m.user_module.lookup(sig).rulechain.next
    error = get_uncaught_error(t, e)
    assert error.rule is rule

def test_exception_knows_rule_toplevel():
    # toplevel rule
    e = get_engine("")
    m = e.modulewrapper
    error = get_uncaught_error("drumandbass(X).", e)
    assert error.rule is m.current_module._toplevel_rule

def test_exception_knows_rule_change_back_to_earlier_rule():
    e = get_engine("""
        g(a).
        f(X) :- g(X), drumandbass(X).
    """)
    (t, vs) = get_query_and_vars("f(X).")

    m = e.modulewrapper
    sig = t.signature()
    rule = m.user_module.lookup(sig).rulechain

    error = get_uncaught_error(t, e)
    assert error.rule is rule

def test_exception_knows_builtin_signature():
    e = get_engine("""
        f(X, Y) :- atom_length(X, Y).
    """)
    error = get_uncaught_error("f(1, Y).", e)
    assert error.sig_context == Signature.getsignature("atom_length", 2)
