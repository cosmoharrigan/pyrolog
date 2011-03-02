import py
from prolog.interpreter.test.tool import assert_true, \
get_engine, assert_false, collect_all
from prolog.interpreter.continuation import Engine

loc = "../../prolog_modules/"
e = get_engine("""
:- use_module('%s%s').
""" % (loc, "dcg"))

def test_a_to_b():
    assert_true("""
    trans((a --> b), X),
    X = (a(X1, X2) :- b(X1, X2)).
    """, e)

def test_a_to_b_c():
    assert_true("""
    trans((a --> b, c), X),
    X = (a(X1, X3) :- b(X1, X2), c(X2, X3)).
    """, e)

def test_single_terminal():
    assert_true("""
    trans((a --> [b]), X),
    X = (a([b|X1], X1) :- true).
    """, e)

def test_terminal_nonterminal():
    assert_true("""
    trans((a --> [c], b), X),
    X = (a([c|Y1], Y2) :- b(Y1, Y2)).
    """, e)

def test_nonterminal_terminal():
    assert_true("""
    trans((a --> b, [c]), X),
    X = (a(X1, X3) :- b(X1, X2), X2=[c|X3]).
    """, e)

def test_nonterminal_terminal_terminal():
    assert_true("""
    trans((a --> b, [c], [d]), X),
    X = (a(X1, X3) :- b(X1, X2), X2=[c, d|X3]).
    """, e)

def test_terminal_terminal():
    assert_true("""
    trans((a --> [b], [c]), X),
    X = (a([b, c|X], X) :- true).
    """, e)

def test_nonterminal_param_1():
    assert_true("""
    trans((a(X) --> b), R),
    R = (a(X, X1, X2) :- b(X1, X2)).
    """, e)

def test_nonterminal_param_2():
    assert_true("""
    trans((a(X, Y) --> b(Y)), R),
    R = (a(X, Y, X1, X2) :- b(Y, X1, X2)).
    """, e)

def test_curly():
    assert_true("""
    trans((a --> {X=1}), R),
    R = (a(X1, X2) :- X=1, X2=X1).
    """, e)

def test_nonterminal_curly():
    assert_true("""
    trans((a --> b, {X=1}), R),
    R = (a(X1, X2) :- b(X1, X3), X=1, X2=X3).
    """, e)

def test_nonterminal_nonterminal_curly():
    assert_true("""
    trans((a --> b, c, {X=1}), R),
    R = (a(X1, X2) :- b(X1, X3), c(X3, X4), X=1, X2=X4).
    """, e)

def test_curly_nonterminal():
    assert_true("""
    trans((a --> {X=1}, b), R),
    R = (a(X1, X2) :- X=1, b(X1, X2)).
    """, e)

def test_curly_multiple_nonterminal():
    assert_true("""
    trans((a --> {X=1, Y=2, Z=3}, b), R),
    R = (a(X1, X2) :- (X=1, Y=2, Z=3), b(X1, X2)).
    """, e)

def test_curly_nonterminal_curly_nonterminal():
    assert_true("""
    trans((a --> {X=1}, b, {Y=2}, c), R),
    R = (a(X1, X2) :- X=1, b(X1, X3), Y=2, c(X3, X2)).
    """, e)

def test_curly_terminal():
    assert_true("""
    trans((a --> {X=1}, [b]), R),
    R = (a(X1, X2) :- X=1, X1=[b|X2]).
    """, e)

def test_dcg_integration_1():
    assert_true("""
    trans((a --> {X=1, Y=2}, [b, c], b(Y)), R),
    R = (a(X1, X2) :- (X=1, Y=2), X1=[b, c|X4], b(Y, X4, X2)).
    """, e)

def test_curly_multiple_1():
    assert_true("""
    trans((a --> {X=1, Y=2}), R),
    R = (a(X1, X2) :- X=1, Y=2, X1=X2).
    """, e)

def test_curly_multiple_2():
    assert_true("""
    trans((a --> {X=1, Y=2, Z=3}), R),
    R = (a(X1, X2) :- X=1, Y=2, Z=3, X1=X2).
    """, e)

# DCG integration tests, i. e. check translated rules
# ___________________________________________________

def make_engine():
    e = get_engine("""
    :- use_module('%s%s').
    """ % (loc, "dcg"))
    return e

def test_integration_1():
    assert_true("""
    trans((a1 --> [b], [c]), R1),
    assert(R1),
    a1([b, c], []).
    """, e)

def test_integration_2():
    assert_true("""
    trans((a2 --> b2, c2, [d]), R1),
    trans((b2 --> [b]), R2),
    trans((c2 --> [c]), R3),
    assert(R1), assert(R2), assert(R3),
    a2([b, c, d], []).
    """, e)

def test_integration_3():
    assert_true("""
    trans((s --> np, vp), R1), assert(R1),
    trans((np --> det, n), R2), assert(R2),
    trans((vp --> tv, np), R3), assert(R3),
    trans((vp --> v), R4), assert(R4),
    trans((det --> [the]), R5), assert(R5),
    trans((det --> [a]), R6), assert(R6),
    trans((det --> [every]), R7), assert(R7),
    trans((n --> [man]), R8), assert(R8),
    trans((n --> [woman]), R9), assert(R9),
    trans((n --> [park]), R10), assert(R10),
    trans((tv --> [loves]), R11), assert(R11),
    trans((tv --> [likes]), R12), assert(R12),
    trans((n --> [park]), R13), assert(R13),
    s([a, man, loves, the, woman], []),
    s([every, woman, likes, a, park], []).
    """, e)
    assert_false("""
    s([every, every, woman, likes, a, man], []).
    """, e)
    assert_true("s([the, woman, loves, the, man], []).", e)

def test_integration_4():
    assert_true("""
    trans((sb --> ab, [or], sb), R1), assert(R1),
    trans((sb --> ab), R2), assert(R2),
    trans((ab --> bb, [and], sb), R3), assert(R3),
    trans((ab --> bb), R4), assert(R4),
    trans((bb --> [true]), R5), assert(R5),
    trans((bb --> [false]), R6), assert(R6),
    trans((bb --> ['('], sb, [')']), R7), assert(R7),
    trans((bb --> [not, '('], sb, [')']), R8), assert(R8).
    """, e)
    assert_true("sb([true, or, false], []).", e)
    assert_true("sb([false, and, '(', false, ')'], []).", e)
    assert_true("sb([not, '(', true, ')'], []).", e)
    assert_true("sb([true, and, false, or, true, and, not, '(', false, or, true, ')'], []).", e)
    assert_true("sb(['(', false, ')'], []).", e)

    assert_false("sb([true, true], []).", e)
    assert_false("sb([true, '(', false], []).", e)
    assert_false("sb([true, or, true, and, not, false], []).", e)
    assert_false("sb([not, '(', false, ')', or], []).", e)

def test_integration_5():
    assert_true("""
    trans((expr --> term, addterm), R1), assert(R1),
    trans((addterm --> []), R2), assert(R2),
    trans((addterm --> [+], expr), R3), assert(R3),
    trans((term --> factor, multfactor), R4), assert(R4),
    trans((multfactor --> []), R5), assert(R5),
    trans((multfactor --> [*], term), R6), assert(R6),
    trans((factor --> [I], {integer(I)}), R7), assert(R7),
    trans((factor --> ['('], expr, [')']), R8), assert(R8).
    """, e)

    assert_true("expr([1, '+', 2], []).", e)
    assert_true("expr([1, '*', '(', 2, '+', 3, ')'], []).", e)
    assert_true("expr([1, '*', '(', 2, '+', '(', 3, ')', ')'], []).", e)
    assert_true("expr([1000], []).", e)

    assert_false("expr([100, 1000], []).", e)
    assert_false("expr([a], []).", e)
    assert_false("expr([1, '+', '*', '2'], []).", e)
