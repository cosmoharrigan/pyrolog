import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter import term
from prolog.interpreter.helper import wrap_list, is_term
from prolog.interpreter.memo import CopyMemo
from prolog.interpreter.term import Var, AttVar, Callable

@expose_builtin("term_variables", unwrap_spec=["obj", "obj"])
def impl_term_variables(engine, heap, prolog_term, variables):
    term_variables(engine, heap, prolog_term, variables)


def term_variables(engine, heap, prolog_term, variables, consider_attributes=False):
    varlist = []
    if consider_attributes:
        varc = variables.copy(heap, CopyMemo())
    seen = {}
    todo = [prolog_term]
    while todo:
        t = todo.pop()
        if isinstance(t, Var):
            value = t.getvalue(heap)
            if isinstance(value, AttVar) and value.atts and value not in seen:
                varlist.append(value)
                seen[value] = None
                if consider_attributes:
                    X = Var()
                    prolog_list = Callable.build(".", [value, X])
                    prolog_list.unify(varc, heap)
                    varc = X
        elif is_term(t):
            numargs = t.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(t.argument_at(i))
    wrap_list(varlist).unify(variables, heap)
