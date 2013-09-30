import py, pytest

from prolog.interpreter.parsing import get_engine
from prolog.interpreter.parsing import get_query_and_vars
from prolog.interpreter.error import UncaughtError

def test_errstr():
    e = get_engine("""
        f(X) :- drumandbass(X).
    """)
    (t, vs) = get_query_and_vars("f(X).")

    m = e.modulewrapper

    info = pytest.raises(UncaughtError, e.run_query_in_current, t)
    assert info.value.get_errstr(e) == "Undefined procedure: drumandbass/1"

def test_exception_knows_rule():
    e = get_engine("""
        f(1).
        f(X) :- drumandbass(X).
    """)
    (t, vs) = get_query_and_vars("f(X), X = 2.")

    m = e.modulewrapper
    sig = t.argument_at(0).signature()
    rule = m.user_module.lookup(sig).rulechain.next

    info = pytest.raises(UncaughtError, e.run_query_in_current, t)
    assert info.value.rule is rule

