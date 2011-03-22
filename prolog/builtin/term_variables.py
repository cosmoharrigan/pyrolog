import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter import term
from prolog.interpreter.helper import wrap_list, is_term
from prolog.interpreter.memo import CopyMemo
from prolog.interpreter.term import Var, AttVar, Callable

from prolog.interpreter.error import UnificationFailed

@expose_builtin("term_variables", unwrap_spec=["obj", "obj"])
def impl_term_variables(engine, heap, prolog_term, variables):
    term_variables(engine, heap, prolog_term, variables)


def term_variables(engine, heap, prolog_term, variables, consider_attributes=False):
    varlist = []
    #if consider_attributes:
    varc = variables
    seen = {}
    todo = [prolog_term]
    cls = Var
    if consider_attributes:
        cls = AttVar
    while todo:
        t = todo.pop()
        value = t.dereference(heap)
        if isinstance(value, cls):
            if consider_attributes and not value.atts:
                continue
            if value not in seen:
                varlist.append(value.dereference(heap))
                seen[value] = None
                #if consider_attributes:
                X = Var()
                prolog_list = Callable.build(".", [value, X])
                prolog_list.unify(varc, heap)
                varc = X
        elif is_term(value):
            numargs = value.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(value.argument_at(i))
    wrap_list(varlist).unify(variables, heap)
