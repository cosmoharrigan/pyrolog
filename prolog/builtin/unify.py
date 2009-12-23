import py
from prolog.interpreter import arithmetic
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter import engine, helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# comparison and unification of terms

@expose_builtin("=", unwrap_spec=["raw", "raw"])
def impl_unify(engine, heap, obj1, obj2):
    obj1.unify(obj2, heap)

@expose_builtin("unify_with_occurs_check",
                unwrap_spec=["raw", "raw"])
def impl_unify_with_occurs_check(engine, heap, obj1, obj2):
    obj1.unify(obj2, heap, occurs_check=True)

@expose_builtin("\\=", unwrap_spec=["raw", "raw"])
def impl_does_not_unify(engine, heap, obj1, obj2):
    branch = heap.branch()
    try:
        obj1.unify(obj2, heap)
    except error.UnificationFailed:
        heap.revert_and_discard(branch)
        return
    heap.discard(branch)
    raise error.UnificationFailed()


for ext, prolog, python in [("eq", "==", "== 0"),
                            ("ne", "\\==", "!= 0"),
                            ("lt", "@<", "== -1"),
                            ("le", "@=<", "!= 1"),
                            ("gt", "@>", "== 1"),
                            ("ge", "@>=", "!= -1")]:
    exec py.code.Source("""
@expose_builtin(prolog, unwrap_spec=["obj", "obj"])
def impl_standard_comparison_%s(engine, heap, obj1, obj2):
    c = term.cmp_standard_order(obj1, obj2, heap)
    if not c %s:
        raise error.UnificationFailed()""" % (ext, python)).compile()
 
