""" Helper functions for dealing with prolog terms"""

from prolog.interpreter import term
from prolog.interpreter import error

emptylist = term.Callable.build("[]")

def wrap_list(python_list):
    curr = emptylist
    for i in range(len(python_list) - 1, -1, -1):
        curr = term.Callable.build(".", [python_list[i], curr])
    return curr

def unwrap_list(prolog_list):
    result = []
    curr = prolog_list
    while isinstance(curr, term.Callable) and curr.signature() == './2':
        result.append(curr.argument_at(0))
        curr = curr.argument_at(1)
    if isinstance(curr, term.Callable) and curr.name()== "[]":
        return result
    error.throw_type_error("list", prolog_list)

def is_callable(var, engine):
    return isinstance(var, term.Callable)

def ensure_callable(var):
    if isinstance(var, term.Var):
        error.throw_instantiation_error()
    elif isinstance(var, term.Callable):
        return var
    else:
        error.throw_type_error("callable", var)

def unwrap_int(obj):
    if isinstance(obj, term.Number):
        return obj.num
    elif isinstance(obj, term.Float):
        f = obj.floatval; i = int(f)
        if f == i:
            return i
    error.throw_type_error('integer', obj)

def unwrap_atom(obj):
    if isinstance(obj, term.Atom):
        return obj.name()    
    error.throw_type_error('atom', obj)

def unwrap_predicate_indicator(predicate):
    if not isinstance(predicate, term.Term):
        error.throw_type_error("predicate_indicator", predicate)
        assert 0, "unreachable"
    if not predicate.name()== "/" or predicate.argument_count() != 2:
        error.throw_type_error("predicate_indicator", predicate)
    name = unwrap_atom(predicate.argument_at(0))
    arity = unwrap_int(predicate.argument_at(1))
    return name, arity

def ensure_atomic(obj):
    if not is_atomic(obj):
        error.throw_type_error('atomic', obj)
    return obj

def is_atomic(obj):
    return (isinstance(obj, term.Atom) or isinstance(obj, term.Float) or 
            isinstance(obj, term.Number))

def is_term(obj):
    return isinstance(obj, term.Callable) and obj.argument_count() > 0

def convert_to_str(obj):
    if isinstance(obj, term.Var):
        error.throw_instantiation_error()
    if isinstance(obj, term.Atom):
        return obj.name()    
    elif isinstance(obj, term.Number):
        return str(obj.num)
    elif isinstance(obj, term.Float):
        return str(obj.floatval)
    error.throw_type_error("atomic", obj)

