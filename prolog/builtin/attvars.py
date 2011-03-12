from prolog.builtin.register import expose_builtin
from prolog.interpreter import continuation
from prolog.interpreter.term import AttVar, Var
from prolog.interpreter.error import UnificationFailed

@expose_builtin("attvar", unwrap_spec=["obj"])
def impl_attvar(engine, heap, obj):
    if not isinstance(obj, AttVar):
        raise UnificationFailed

@expose_builtin("put_attr", unwrap_spec=["obj", "atom", "obj"])
def impl_put_attr(engine, heap, var, attr, value):
    if isinstance(var, AttVar):
        var.atts[attr] = value
    elif isinstance(var, Var):
        attvar = AttVar()
        attvar.atts[attr] = value
        var.unify(attvar, heap)
    else:
        # XXX raise representation error
        pass

@expose_builtin("get_attr", unwrap_spec=["obj", "atom", "obj"])
def impl_get_attr(engine, heap, var, attr, value):
    if not isinstance(var, Var):
        error.throw_instantiation_error(var)
    if not isinstance(var, AttVar):
        raise UnificationFailed
    try:
        value.unify(var.atts[attr], heap)
    except KeyError:
        raise UnificationFailed
        
