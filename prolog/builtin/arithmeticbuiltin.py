import py
from prolog.interpreter import helper, term, error, continuation
from prolog.builtin.register import expose_builtin
# ___________________________________________________________________
# arithmetic


class BetweenContinuation(continuation.ChoiceContinuation):
    def __init__(self, engine, scont, fcont, heap, lower, upper, varorint):
        continuation.ChoiceContinuation.__init__(self, engine, scont.module, scont)
        self.undoheap = heap
        self.orig_fcont = fcont
        self.lower = lower
        self.upper = upper
        self.varorint = varorint
        self.i = lower
        
    def activate(self, fcont, heap):
        if self.i <= self.upper:
            fcont, heap = self.prepare_more_solutions(fcont, heap)
            try:
                self.varorint.unify(term.Number(self.i), heap)
            except error.UnificationFailed, e:
                return fcont, self.orig_fcont, heap
            finally:
                self.i +=1
            return self.nextcont, fcont, heap
        raise error.UnificationFailed()
        
@expose_builtin("between", unwrap_spec=["int", "int", "obj"],
               handles_continuation=True)
def impl_between(engine, heap, lower, upper, varorint, scont, fcont):
    if isinstance(varorint, term.Var):
        bc = BetweenContinuation(engine, scont, fcont, heap, 
                                                        lower, upper, varorint)
        return bc, fcont, heap
    else:
        integer = helper.unwrap_int(varorint)
        if not (lower <= integer <= upper):
            raise error.UnificationFailed
    return scont, fcont, heap

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
 
