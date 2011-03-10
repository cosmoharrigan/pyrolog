import py
from prolog.builtin.register import expose_builtin
from prolog.interpreter import term
from prolog.interpreter.helper import wrap_list, is_term

@expose_builtin("term_variables", unwrap_spec=["obj", "obj"])
def impl_term_variables(engine, heap, prolog_term, variables):
    varlist, _ = find_variables(prolog_term, [], {})
    wrap_list(varlist).unify(variables, heap)

def find_variables(prolog_term, variables, vardict):
    if isinstance(prolog_term, term.Var) and not prolog_term in vardict:
        variables.append(prolog_term)
        vardict[prolog_term] = True
    elif is_term(prolog_term):
        numargs = prolog_term.argument_count()
        for i in range(numargs):
            variables, vardict = find_variables(prolog_term.argument_at(i),
                    variables, vardict)
    # else return parameters
    return variables, vardict
