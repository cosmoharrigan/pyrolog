import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter import term
from prolog.interpreter.helper import wrap_list, is_term

@expose_builtin("term_variables", unwrap_spec=["obj", "obj"])
def impl_term_variables(engine, heap, prolog_term, variables):
    varlist = []
    seen = {}
    todo = [prolog_term]
    while todo:
        prolog_term = todo.pop().dereference(None)
        if isinstance(prolog_term, term.Var):
            if prolog_term not in seen:
                varlist.append(prolog_term)
                seen[prolog_term] = None
        elif is_term(prolog_term):
            numargs = prolog_term.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(prolog_term.argument_at(i)) 
    wrap_list(varlist).unify(variables, heap)
