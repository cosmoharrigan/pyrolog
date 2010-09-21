import py
import sys
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.continuation import Heap, Engine
from prolog.interpreter import error
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true
from prolog.interpreter.term import Number, Float, BigInt
import prolog.interpreter.arithmetic # has side-effects, changes Number etc

from pypy.rlib.rbigint import rbigint

class TestArithmeticMethod(object):
    def test_add(self):
        f1 = Float(5.1)
        f2 = Float(10.1)
        assert f1.arith_add(f2).floatval == 15.2

        n0 = Number(1)
        n1 = Number(2)
        assert n0.arith_add(n1).num == 3

        n2 = Number(2)
        f3 = Float(3.2)
        assert n2.arith_add(f3).floatval == 5.2
        assert f3.arith_add(n2).floatval == 5.2

        b1 = BigInt(rbigint.fromdecimalstr('50000000000000000000000'))
        b2 = BigInt(rbigint.fromdecimalstr('10000000000000000000001'))
        assert b1.arith_add(b2).value.str() == '60000000000000000000001'

        n3 = Number(sys.maxint)
        assert n3.arith_add(n0).value.str() == str(sys.maxint + 1)

        b = BigInt(rbigint.fromdecimalstr('100000000000000000000000000000'))
        f = Float(1.5)
        assert b.arith_add(f).floatval == 100000000000000000000000000001.5
        assert f.arith_add(b).floatval == 100000000000000000000000000001.5

        assert b.arith_add(n0).value.tofloat() == 100000000000000000000000000001.0
        assert n0.arith_add(b).value.tofloat() == 100000000000000000000000000001.0

        # -------------------- test subtraction --------------------------
        n1 = Number(5)
        n2 = Number(10)
        assert n1.arith_sub(n2).num == -5
        assert n2.arith_sub(n1).num == 5

        f1 = Float(10.5)
        f2 = Float(30.6)
        assert f1.arith_sub(f2).floatval == -20.1
        assert f2.arith_sub(f1).floatval == 20.1

        b1 = BigInt(rbigint.fromdecimalstr('10000000000000000000000000000000000000'))
        b2 = BigInt(rbigint.fromdecimalstr('20000000000000000000000000000000000000'))
        assert b1.arith_sub(b2).value.tofloat() == -10000000000000000000000000000000000000.0
        assert b2.arith_sub(b1).value.tofloat() == 10000000000000000000000000000000000000.0




def test_simple():
    assert_true("X is 1 + 2, X = 3.")
    assert_true("X is 1.2 + 2.8, X = 4.")
    assert_false("X is 1.1 + 2.8, X = 4.0.")
    assert_true("X is 1 - 2, X = -1.")
    assert_true("X is 1.2 - 1.2, X = 0.")
    assert_true("X is 2 * -2, X = -4.")
    assert_true("X is 2 * -2.1, X = -4.2.")
    assert_true("X is 2 + -2, X = 0.")
    assert_true("X is 2 // -2, X = -1.")

    assert_true("X is 1 << 4, X = 16.")
    assert_true("X is 128 >> 7, X = 1.")
    assert_true("X is 12 \\/ 10, X = 14.")
    assert_true("X is 12 /\\ 10, X = 8.")
    assert_true("X is 12 xor 10, X = 6.")

    assert_true("X is max(12, 13), X = 13.")
    assert_true("X is min(12, 13), X = 12.")
    assert_true("X is max(12, 13.9), X = 13.9.")
    assert_true("X is min(12.1, 13), X = 12.1.")

    assert_true("X is abs(42), X = 42.")
    assert_true("X is abs(-42), X = 42.")
    assert_true("X is abs(42.42), X = 42.42.")
    assert_true("X is abs(-42.42), X = 42.42.")

    assert_true("X is round(0), X = 0.")
    assert_true("X is round(0.3), X = 0.")
    assert_true("X is round(0.4), X = 0.")
    assert_true("X is round(0.5), X = 1.")
    assert_true("X is round(0.6), X = 1.")
    assert_true("X is round(1), X = 1.")
    assert_true("X is round(-0.3), X = 0.")
    assert_true("X is round(-0.4), X = 0.")
    assert_true("X is round(-0.5), X = 0.")
    #assert_true("X is round(-0.6), X = -1.") #XXX fix round
    #assert_true("X is round(-1), X = -1.")

    assert_true("X is ceiling(0), X = 0.")
    assert_true("X is ceiling(0.3), X = 1.")
    assert_true("X is ceiling(0.4), X = 1.")
    assert_true("X is ceiling(0.5), X = 1.")
    assert_true("X is ceiling(0.6), X = 1.")
    assert_true("X is ceiling(1), X = 1.")
    assert_true("X is ceiling(-0.3), X = 0.")
    assert_true("X is ceiling(-0.4), X = 0.")
    assert_true("X is ceiling(-0.5), X = 0.")
    assert_true("X is ceiling(-0.6), X = 0.")
    assert_true("X is ceiling(-1), X = -1.")

    assert_true("X is floor(0), X = 0.")
    assert_true("X is floor(0.3), X = 0.")
    assert_true("X is floor(0.4), X = 0.")
    assert_true("X is floor(0.5), X = 0.")
    assert_true("X is floor(0.6), X = 0.")
    assert_true("X is floor(1), X = 1.")
    assert_true("X is floor(-0.3), X = -1.")
    assert_true("X is floor(-0.4), X = -1.")
    assert_true("X is floor(-0.5), X = -1.")
    assert_true("X is floor(-0.6), X = -1.")
    assert_true("X is floor(-1), X = -1.")

    assert_true("X is float_integer_part(0), X = 0.")
    assert_true("X is float_integer_part(0.3), X = 0.")
    assert_true("X is float_integer_part(0.4), X = 0.")
    assert_true("X is float_integer_part(0.5), X = 0.")
    assert_true("X is float_integer_part(0.6), X = 0.")
    assert_true("X is float_integer_part(1), X = 1.")
    assert_true("X is float_integer_part(-0.3), X = 0.")
    assert_true("X is float_integer_part(-0.4), X = 0.")
    assert_true("X is float_integer_part(-0.5), X = 0.")
    assert_true("X is float_integer_part(-0.6), X = 0.")
    assert_true("X is float_integer_part(-1), X = -1.")

    assert_true("X is float_fractional_part(1), X = 0.")
    assert_true("X is float_fractional_part(2), X = 0.")
    assert_true("X is float_fractional_part(-1), X = 0.")
    assert_true("X is float_fractional_part(1.2), Y is 1.2 - 1, X = Y.")
    assert_true("X is float_fractional_part(1.4), Y is 1.4 - 1, X = Y.")
    assert_true("X is float_fractional_part(1.6), Y is 1.6 - 1, X = Y.")
    assert_true("X is float_fractional_part(-1.2), X is -1.2 + 1, X = Y.")
    assert_true("X is float_fractional_part(-1.4), X is -1.4 + 1, X = Y.")
    assert_true("X is float_fractional_part(-1.6), X is -1.6 + 1, X = Y.")

    assert_true("X is 2 ** 4, X = 16.")

def test_comparison():
    assert_true("1 =:= 1.0.")
    assert_true("1 + 1 > 1.")
    assert_true("1 + 0.001 >= 1 + 0.001.")
    assert_true("1 + 0.001 =< 1 + 0.001.")
    assert_false("1 > 1.")
    assert_true("1.1 > 1.")
    assert_false("1 =\\= 1.0.")
    assert_true("1 =\\= 32.")
