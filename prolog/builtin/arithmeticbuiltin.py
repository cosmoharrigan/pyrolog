import py
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin

# ___________________________________________________________________
# arithmetic


@expose_builtin("between", unwrap_spec=["int", "int", "obj"],
                handles_continuation=True)
def impl_between(engine, heap, lower, upper, varorint, continuation):
    if isinstance(varorint, term.Var):
        for i in range(lower, upper):
            oldstate = heap.branch()
            try:
                varorint.unify(term.Number(i), heap)
                result = continuation.call(engine, choice_point=True)
                heap.discard(oldstate)
                return result
            except error.UnificationFailed:
                heap.revert(oldstate)
        varorint.unify(term.Number(upper), heap)
        return continuation.call(engine, choice_point=False)
    else:
        integer = helper.unwrap_int(varorint)
        if not (lower <= integer <= upper):
            raise error.UnificationFailed
    return continuation.call(engine, choice_point=False)

@expose_builtin("is", unwrap_spec=["raw", "arithmetic"])
def impl_is(engine, heap, var, num):
    var.unify(num, heap)

for ext, prolog, python in [("eq", "=:=", "=="),
                            ("ne", "=\\=", "!="),
                            ("lt", "<", "<"),
                            ("le", "=<", "<="),
                            ("gt", ">", ">"),
                            ("ge", ">=", ">=")]:
    exec py.code.Source("""
@expose_builtin(prolog, unwrap_spec=["arithmetic", "arithmetic"])
def impl_arith_%s(engine, heap, num1, num2):
    eq = False
    if isinstance(num1, term.Number):
        if isinstance(num2, term.Number):
            if not (num1.num %s num2.num):
                raise error.UnificationFailed()
            else:
                return
        n1 = num1.num
    else:
        assert isinstance(num1, term.Float)
        n1 = num1.floatval
    if isinstance(num2, term.Number):
        n2 = num2.num
    else:
        assert isinstance(num2, term.Float)
        n2 = num2.floatval
    eq = n1 %s n2
    if not eq:
        raise error.UnificationFailed()""" % (ext, python, python)).compile()
 
