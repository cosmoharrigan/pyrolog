from prolog.builtin.register import expose_builtin
from prolog.interpreter import continuation
from prolog.interpreter.term import AttVar, Var, Callable, Atom
from prolog.interpreter.error import UnificationFailed,\
throw_representation_error
from prolog.interpreter.helper import wrap_list, is_term, unwrap_list
from prolog.interpreter.signature import Signature
from prolog.interpreter.memo import CopyMemo

conssig = Signature.getsignature(".", 2)

@expose_builtin("attvar", unwrap_spec=["obj"])
def impl_attvar(engine, heap, obj):
    if not isinstance(obj.getvalue(heap), AttVar) or not obj.atts:
        raise UnificationFailed()

@expose_builtin("put_attr", unwrap_spec=["obj", "atom", "obj"])
def impl_put_attr(engine, heap, var, attr, value):
    if isinstance(var, AttVar):
        heap.add_trail_atts(var, attr)
        var.atts[attr] = value
    elif isinstance(var, Var):
        attvar = AttVar()
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
"""
@expose_builtin("term_attvars", unwrap_spec=["obj", "obj"])
def impl_term_attvars(engine, heap, prolog_term, variables):
    if (isinstance(variables, Callable) and variables.signature().eq(conssig)
            or isinstance(variables, Atom) and variables.name() == "[]"):
        impl_term_attvars_fail_fast(engine, heap, prolog_term, variables,
                len(unwrap_list(variables)))
    else:
        impl_term_attvars_default(engine, heap, prolog_term, variables)

def impl_term_attvars_fail_fast(engine, heap, prolog_term, variables, length):
    varlist = []
    seen = {}
    todo = [prolog_term]
    n = 0
    while todo:
        t = todo.pop()
        if isinstance(t, Var):
            value = t.getvalue(heap)
            if isinstance(value, AttVar) and value.atts and value not in seen:
                if n == length:
                    raise UnificationFailed()
                varlist.append(value)
                seen[value] = None
                n += 1
        elif is_term(t):
            numargs = t.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(t.argument_at(i))
    wrap_list(varlist).unify(variables, heap)

def impl_term_attvars_default(engine, heap, prolog_term, variables):
    varlist = []
    seen = {}
    todo = [prolog_term]
    while todo:
        t = todo.pop()
        if isinstance(t, Var):
            value = t.getvalue(heap)
            if isinstance(value, AttVar) and value.atts and value not in seen:
                varlist.append(value)
                seen[value] = None
        elif is_term(t):
            numargs = t.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(t.argument_at(i))
    wrap_list(varlist).unify(variables, heap)
"""
@expose_builtin("term_attvars", unwrap_spec=["obj", "obj"])
def impl_term_attvars(engine, heap, prolog_term, variables):
    varlist = []
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
                X = Var()
                prolog_list = Callable.build(".", [value, X])
                prolog_list.unify(varc, heap)
                varc = X
        elif is_term(t):
            numargs = t.argument_count()
            for i in range(numargs - 1, -1, -1):
                todo.append(t.argument_at(i))
    wrap_list(varlist).unify(variables, heap)
