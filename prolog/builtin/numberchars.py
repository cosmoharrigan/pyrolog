import py
from prolog.interpreter import term, error
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Callable
from prolog.interpreter.term import specialized_term_classes
from pypy.rlib.rarithmetic import ovfcheck
from pypy.rlib.rbigint import rbigint
from prolog.interpreter.signature import Signature
from prolog.interpreter.helper import wrap_list

conssig = Signature.getsignature(".", 2)
num_atom_names = [str(i) for i in range(10)]

def num_to_list(num):
    from prolog.interpreter.helper import wrap_list
    if isinstance(num, term.Number):
        s = str(num.num)
    elif isinstance(num, term.Float):
        s = str(num.floatval)
    elif isinstance(num, term.BigInt):
        s = num.value.str()
    else:
        error.throw_type_error("number", num)
    return wrap_list([Callable.build(c) for c in s])


def cons_to_num(charlist):
    from prolog.interpreter.helper import unwrap_list, unwrap_atom
    unwrapped = unwrap_list(charlist)
    numlist = []
    for elem in unwrapped:
        if not isinstance(elem, term.Atom):
            error.throw_type_error("text", charlist)
        digit = elem.name()
        numlist.append(digit)
    
    numstr = "".join(numlist)

    try:
        return term.Number(ovfcheck(int(numstr)))
    except OverflowError:
        return term.BigInt(rbigint.fromdecimalstr(numstr))
    except ValueError:
        pass
    try:
        return term.Float(float(numstr))
    except ValueError:
        error.throw_syntax_error("Illegal number")


@expose_builtin("number_chars", unwrap_spec=["obj", "obj"])
def impl_number_chars(engine, heap, num, charlist):
    if not isinstance(charlist, term.Var):
        cons_to_num(charlist).unify(num, heap)
    else:
        if isinstance(num, term.Var):
            error.throw_instantiation_error(num)
        else:
            num_to_list(num).unify(charlist, heap)
