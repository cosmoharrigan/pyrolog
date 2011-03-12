from prolog.builtin.register import expose_builtin
from prolog.interpreter import continuation
from prolog.interpreter.term import AttVar
from prolog.interpreter.error import UnificationFailed

@expose_builtin("attvar", unwrap_spec=["obj"])
def impl_attvar(engine, heap, obj):
    if not isinstance(obj, AttVar):
        raise UnificationFailed
