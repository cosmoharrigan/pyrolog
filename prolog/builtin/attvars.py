from prolog.builtin.register import expose_builtin
from prolog.interpreter import continuation
from prolog.interpreter.term import AttVar, Var
from prolog.interpreter.error import UnificationFailed,\
throw_representation_error
from prolog.interpreter.helper import wrap_list

@expose_builtin("attvar", unwrap_spec=["obj"])
def impl_attvar(engine, heap, obj):
    if not (isinstance(obj, Var) and isinstance(obj.getvalue(heap), AttVar)):
        raise UnificationFailed()

@expose_builtin("put_attr", unwrap_spec=["obj", "atom", "obj"])
def impl_put_attr(engine, heap, var, attr, value):
    if isinstance(var, AttVar):
        heap.add_trail_atts(var, attr)
        var.atts[attr] = value
    elif isinstance(var, Var):
        attvar = AttVar(engine)
        attvar.atts[attr] = value
        var.unify(attvar, heap)
    else:
        throw_representation_error("put_attr/3",
                "argument must be unbound (1-st argument)")

@expose_builtin("get_attr", unwrap_spec=["obj", "atom", "obj"])
def impl_get_attr(engine, heap, var, attr, value):
    if not isinstance(var, Var):
        error.throw_instantiation_error(var)
    if not isinstance(var, AttVar):
        raise UnificationFailed()
    try:
        value.unify(var.atts[attr], heap)
    except KeyError:
        raise UnificationFailed()
 
@expose_builtin("del_attr", unwrap_spec=["obj", "atom"])
def impl_del_attr(engine, heap, var, attr):
    if isinstance(var, AttVar):
        heap.add_trail_atts(var, attr)
        var.atts.pop(attr)
        if var.atts == {}:
            var.unify(Var(), heap)

@expose_builtin("term_attvars", unwrap_spec=["obj", "obj"])
def impl_term_attvars(engine, heap, prolog_term, variables):
    varlist = []
    seen = {}
    todo = [prolog_term]
    while todo:
        t = todo.pop()
        if isinstance(t, AttVar) and t not in seen:
            varlist.append(t)
            seen[t] = None
        else:
            numargs = prolog_term.argument_count()
            for i in range(numargs - 1, -1, -1):
                varlist.append(prolog_term.argument_at(i))
    wrap_list(varlist).unify(variables, heap)

