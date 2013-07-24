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

    info = pytest.raises(UncaughtError, e.run, t, m.user_module)
    info.value.get_errstr(e) == "Undefined procedure: drumandbass/1"
