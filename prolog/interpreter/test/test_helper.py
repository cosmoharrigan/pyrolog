import py
from prolog.interpreter.helper import convert_to_str
from prolog.interpreter.term import Callable, BigInt
from pypy.rlib.rbigint import rbigint

def test_convert_to_str():
    assert "a" == convert_to_str(Callable.build("a"))
    assert "100" == convert_to_str(Callable.build("100"))
    assert "1000.111" == convert_to_str(Callable.build("1000.111"))
    assert ("100000000000000000000" == 
            convert_to_str(Callable.build("100000000000000000000")))
    assert "1" == convert_to_str(BigInt(rbigint.fromint(1)))
    assert ("-1000000000000000" == 
            convert_to_str(BigInt(rbigint.fromdecimalstr("-1000000000000000"))))
