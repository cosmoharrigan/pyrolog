import py
import os
from prolog.interpreter.test.tool import get_engine, assert_true, assert_false, prolog_raises
from prolog.interpreter.test.tool import create_file, delete_file, create_dir, delete_dir
from prolog.interpreter.test.tool import collect_all
from prolog.interpreter import term
from prolog.interpreter.signature import Signature
from prolog.interpreter.continuation import Engine

def test_set_currently_parsed_module():
    e = get_engine("""
    f(a).
    """)
    assert e.current_module == e.user_module
    e.add_module("m1", [])
    assert "m1" in e.modules
    mod1 = e.modules["m1"]
    assert mod1.exports == []
    assert mod1.functions == {}
    atom = term.Callable.build("f")
    e.add_rule(atom)
    assert atom.signature() in mod1.functions

def test_module_exports():
    e = get_engine("""
    :- module(m, [g/2]).
    g(a, b).
    f(c, d, e).
    """)
    exports = e.modules["m"].exports
    assert len(exports) == 1 and exports[0].eq(Signature("g", 2))

def test_use_module_with_file():
    e = get_engine("""
    :- use_module(m).
    """, True,
    m = """
    :- module(m, [f/0]).
    f.
    """)
    assert len(e.modules) == 2
    assert_true("f.", e)

def test_module_uses():
    e = get_engine("""
    :- use_module(b).
    """,
    a = """
    :- module(a, [h/1]).
    h(z).
    """,
    b = """
    :- module(b, [f/1]).
    :- use_module(a).
    f(X) :- h(X).
    g(a).
    """)
    assert len(e.modules) == 3

def test_fetch_function():
    e = get_engine("""
    :- use_module(m).
    f(a) :- g(a, b).
    """,
    m = """
    :- module(m, [g/2]).
    g(a, b).
    h(w).
    """)
    f_sig = Signature.getsignature("f", 1)
    g_sig = Signature.getsignature("g", 2)
    h_sig = Signature.getsignature("h", 1)
    user = e.modules["user"]
    m = e.modules["m"]

    assert user.fetch_function(e, g_sig) == m.functions[g_sig]
    assert user.fetch_function(e, h_sig) is None
    assert m.fetch_function(e, g_sig) == m.functions[g_sig]
    assert m.fetch_function(e, f_sig) is None
    assert m.fetch_function(e, h_sig) == m.functions[h_sig]

def test_modules_use_module():
    e = get_engine("""
    :- use_module(m).
    f(X) :- g(X).
    f(b).
    h(a).
    """,
    m = """
    :- module(m, [g/1]).
    g(a).
    h(b).
    """)

    assert_true("f(a).", e)
    assert_true("f(b).", e)
    assert_true("h(a).", e)
    assert_false("h(b).", e)

def test_modules_integration():
    e = get_engine("""
    :- use_module(m).
    f(X) :- g(X).
    h(b).
    both(X, Y) :- f(X), h(Y).
    """,
    m = """
    :- module(m, [g/1]).
    g(X) :- h(X).
    h(a).
    """)

    assert_true("findall(X, h(X), L), L = [b].", e)
    assert_true("both(X, Y), X == a, Y == b.", e)

def test_builtin_module_or():
    e = get_engine("""
    :- use_module(m).
    t :- h, x.
    x.
    """,
    m = """
    :- module(m, [h/0]).
    h :- f; g.
    f.
    g.
    """)
    assert_true("t.", e)

def test_builtin_module_and():
    e = get_engine("""
    :- use_module(m).
    t :- h, x.
    x.
    """,
    m = """
    :- module(m, [h/0]).
    h :- f, g.
    f.
    g.
    """)
    assert_true("t.", e)

def test_catch_error():
    e = get_engine("""
    :- use_module(m).
    h :- catch(f, X, g).
    g.
    """,
    m = """
    :- module(m, [f/0]).
    f :- throw(foo).
    """)
    assert_true("h.", e)

def test_abolish():
    e = get_engine("""
    :- use_module(m).
    f(a).
    """,
    m = """
    :- module(m, [g/1]).
    g(a).
    """)

    assert_true("f(a).", e)
    assert len(e.modules["user"].functions) == 2
    assert_true("abolish(f/1).", e)
    prolog_raises("existence_error(A, B)", "f(a)", e)
    assert_true("g(a).", e)
    assert_true("abolish(g/1).", e)
    prolog_raises("existence_error(A, B)", "g(a)", e)
    assert len(e.modules["user"].functions) == 0
    assert len(e.modules["m"].functions) == 1

def test_if():
    e = get_engine("""
    :- use_module(m).
    f(X) :- (X = b
        -> g(X)
        ; h(X)).
    g(c).
    """,
    m = """
    :- module(m, [h/1]).
    h(a).
    """)

    assert_true("f(a).", e)
    assert_false("f(b).", e)

def test_once():
    e = get_engine("""
    :- use_module(m).
    x :- f, h.
    h.
    """,
    m = """
    :- module(m, [f/0]).
    f :- once(g).
    g.
    """)
    assert_true("x.", e)

def test_module_switch_1():
    e = get_engine("""
    :- use_module(m).
    :- module(m).
    """,
    m = """
    :- module(m, [g/0]).
    g.
    f.
    """)
    assert e.current_module.name == "m"
    assert_true("g.", e)
    assert_true("f.", e)

def test_module_switch_2():
    e = get_engine("""
    :- use_module(m).
    f.
    :- module(m).
    """,
    m = """
    :- module(m, []).
    g.
    """)

    assert e.current_module.name == "m"
    prolog_raises("existence_error(X, Y)", "f", e)
    assert_true("g.", e)
    assert_true("module(user).", e)
    assert e.current_module.name == "user"
    prolog_raises("existence_error(X, Y)", "g", e)
    assert_true("f.", e)

def test_switch_to_nonexistent_module():
    e = get_engine("""
    :- module(m).
    """)
    prolog_raises("existence_error(X, Y)", "x", e)
    assert_true("assert(x).", e)
    assert_true("x.", e)
    assert_true("module(user).", e)
    prolog_raises("existence_error(X, Y)", "x", e)

def test_module_assert_retract():
    e = Engine()
    assert_true("module(m).", e)
    assert_true("assert(x).", e)
    assert_true("asserta(y).", e)
    assert_true("x, y.", e)
    assert_true("module(user).", e)
    assert_false("retract(x).", e)
    assert_false("retract(y).", e)
    assert_true("assert(x).", e)
    assert_true("x.", e)
    assert_true("module(m).", e)
    assert_true("retract(x).", e)
    prolog_raises("existence_error(X, Y)", "x", e)
    assert_true("module(user).", e)
    assert_true("x.", e)

def test_module_prefixing():
    e = get_engine("""
    a.
    """,
    m = """
    :- module(m, []).
    f(a).
    f(b).
    """)
    assert_true("m:f(a), m:f(b).", e)
    assert_true("m:f(a), a.", e)
    prolog_raises("existence_error(X, Y)", "m:a", e)
    assert_true("module(m).", e)
    prolog_raises("existence_error(X, Y)", "a", e)
    assert_true("user:a.", e)

def test_prefix_non_existent_module():
    prolog_raises("existence_error(X, Y)", "a:b")

def test_recursive_use_module():
    # if this test fails, one will recognize it by
    # waiting very long ...
    mod = "m"
    create_file(mod, """
    :- module(m, []).
    :- use_module(m).
    """)

    try:
        e = get_engine("""
        :- use_module(m).
        """)
    finally:
        delete_file(mod)

def test_alternating_recursive_import():
    mod = "m2"
    create_file(mod, """
    :- module(m2, [g/1]).
    :- use_module(m1).
    g(b).
    """)
    
    e = get_engine("""
    :- use_module(m1).
    """,
    m1 = """
    :- module(m1, [f/1]).
    f(a).
    :- use_module(m2).
    """)
    try:
        assert_true("f(X), X = a.", e)
        prolog_raises("existence_error(X, Y)", "g(X)", e)
    finally:
        delete_file(mod)

def test_recursive_ring_import():
    mod2 = "m2"
    mod3 = "m3"

    create_file(mod2, """
    :- module(m2, [g/1]).
    :- use_module(m3).
    g(a).
    """)

    create_file(mod3, """
    :- module(m3, [h/1]).
    :- use_module(m1).
    h(a).
    """)

    e = get_engine("""
    :- use_module(m1).
    z(a).
    """,
    m1 = """
    :- module(m1, [f/1]).
    f(a).
    :- use_module(m2).
    """)
    try:
        assert len(e.modules) == 4
        assert len(e.modules["user"].functions) == 2
        assert len(e.modules["m1"].functions) == 2
        assert len(e.modules["m2"].functions) == 2
        assert len(e.modules["m3"].functions) == 2
        assert_true("z(a).", e)
        assert_true("f(a).", e)
        assert_true("m1:f(a).", e)
        assert_true("m1:g(a).", e)
        assert_true("m2:g(a).", e)
        assert_true("m2:h(a).", e)
        assert_true("m3:h(a).", e)
        assert_true("m3:f(a).", e)
    finally:
        delete_file(mod2)
        delete_file(mod3)

def test_use_same_module_twice():
    # if this test fails, one will recognize it by
    # waiting very long ...
    e = get_engine(
    """
    :- use_module(m1).
    :- use_module(m2).
    h(X) :- g(X), f(X).
    """, True,
    m1 = """
    :- module(m1, [f/1]).
    f(a).
    """,
    m2 = """
    :- module(m2, [g/1]).
    :- use_module(m1).
    g(X) :- f(X).
    """)
    assert_true("h(X), X == a.", e)

def test_impl_use_module():
    from prolog.builtin.modules import impl_use_module
    from prolog.interpreter.heap import Heap
    filecontent = """
    :- module(blub, []).
    """
    e = Engine()
    h = Heap()
    create_file("blub.pl", filecontent)
    try:
        impl_use_module(e, e.user_module, h, term.Callable.build("blub.pl"))
        assert "blub" in e.modules.keys()
    finally:
        delete_file("blub.pl")

    create_file("blub", filecontent)
    e.modules = {}
    try:
        impl_use_module(e, e.user_module, h, term.Callable.build("blub"))
        assert "blub" in e.modules.keys()
    finally:
        delete_file("blub")

def test_add_library_dir():
    e = Engine()
    assert e.libs == {}
    prolog_raises("existence_error(X, Y)", "add_library_dir('does_not_exist')", e)

    lib1 = "__lib1__"
    lib2 = "__lib2__"
    create_dir(lib1)
    create_dir(lib2)

    try:
        assert_true("add_library_dir('%s')." % lib1, e)
        assert_true("add_library_dir('%s')." % lib2, e)
        assert len(e.libs) == 2
    finally:
        delete_dir(lib1)
        delete_dir(lib2)

def test_library_directory():
    e = Engine()
    assert e.libs == {}
    libs = collect_all(e, "library_directory(X).")
    assert len(libs) == 0

    tempdir1 = "__tempdir1__"
    tempdir2 = "__tempdir2__"
    create_dir(tempdir1)
    create_dir(tempdir2)

    try:
        assert_true("add_library_dir('%s')." % tempdir1, e)
        assert_true("add_library_dir('%s')." % tempdir2, e)
        libs = collect_all(e, "library_directory(X).")
        assert len(libs) == 2
        assert len(e.libs) == 2
    finally:
        delete_dir(tempdir1)
        delete_dir(tempdir2)

def test_library_with_files():
    from os.path import abspath
    e = Engine()
    tempdir = "__tempdir__"
    mod1 = "m1"
    mod2 = "m2.pl"

    create_dir(tempdir)
    create_file("%s/%s" % (tempdir, mod1), "")
    create_file("%s/%s" % (tempdir, mod2), "")

    try:
        assert_true("add_library_dir('%s')." % tempdir, e)
        assert len(e.libs) == 1
        path = abspath(tempdir)
        assert "m1" in e.libs[path]
        assert "m2" in e.libs[path]
    finally:
        delete_dir(tempdir)

def test_library():
    tempdir = "__tempdir__"
    mod = "m"

    create_dir(tempdir)
    create_file(tempdir + "/" + mod, """
    :- module(m, [f/1]).
    f(a).
    g.
    """)

    try:
        e = get_engine(":- add_library_dir('%s')." % tempdir)
        assert len(e.libs) == 1
        assert_true("use_module(library('%s'))." % mod, e)
        assert_true("f(a).", e)
        prolog_raises("existence_error(X, Y)", "g", e)
    finally:
        delete_dir(tempdir)

def test_import_list_simple():
    e = get_engine("""
    :- use_module(m, [f/1, g/0]).
    h(X) :- f(X), g.
    """,
    m = """
    :- module(m, [f/1, g/0]).
    f(a).
    g.
    q.
    """)
    assert_true("h(a).", e)
    prolog_raises("existence_error(X, Y)", "q", e)

def test_empty_import_list():
    e = get_engine("""
    :- use_module(m, []).
    """,
    m = """
    :- module(m, [f/1, g/0]).
    f(a).
    g.
    q.
    """)
    assert len(e.modules["user"].functions) == 0
    prolog_raises("existence_error(X, Y)", "f(a)", e)
    prolog_raises("existence_error(X, Y)", "g", e)
    prolog_raises("existence_error(X, Y)", "q", e)

def test_nonexisting_predicates_in_import_list():
    e = get_engine("""
    :- use_module(m, [z/0, g/1]).
    """,
    m = """
    :- module(m, [f/1, g/0]).
    f(a).
    g.
    q.
    """)
    prolog_raises("existence_error(X, Y)", "z", e)
    prolog_raises("existence_error(X, Y)", "g(A)", e)

def test_existing_system_module():
    e = Engine(load_system=True)
    assert e.modules.has_key("system")

# needs list module
def test_access_system_predicate():
    e = Engine(load_system=True)
    assert_true("append([1], [2], [1, 2]).", e)
