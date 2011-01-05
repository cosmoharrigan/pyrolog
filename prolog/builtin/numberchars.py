import py
from prolog.interpreter import term, error
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Callable
from prolog.interpreter.term import specialized_term_classes
from pypy.rlib.rarithmetic import ovfcheck


def get_str_repr(num):
    if isinstance(num, term.Number):
        return str(num.num)[::-1]
    elif isinstance(num, term.Float):
        return str(num.floatval)[::-1]
    elif isinstance(num, term.BigInt):
        numstr = num.value.str()[::-1]
        ret = "".join([digit for digit in numstr])
        if num.value.sign == -1:
            ret = "-" + ret
        return ret
    raise ValueError("expected Number, Float or BigInt")


def num_2_cons(num):
    numstr = get_str_repr(num)
    cons = Callable.build("[]")
    for digit in numstr:
        if digit == "-":
            cons = Callable.build(".", [term.Atom("-"), cons])
        else:
            cons = Callable.build(".", [Callable.build(digit), cons])
    return cons


def cons_2_num(charlist):
    numlist = make_list(charlist, [], False, False)
    if numlist[0] == "-" and len(numlist) == 1:
        error.throw_instantiation_error()
    numstr = "".join(numlist)
    # check if number is a float
    try:
        numlist.index(".")
        return term.Float(float(numstr))
    # must be an integer, since there exists no '.'
    except ValueError:
        try:
            return term.Number(ovfcheck(int(numstr)))
        except OverflowError:
            return term.BigInt(rbigint.fromdecimalstr(numstr))


def make_list(cons, numlist, saw_dot, saw_minus):
    args = cons.arguments()
    innerlist = []
    for arg in args:
        if isinstance(arg, term.Atom):
            name = arg.name()
            if name != "[]":
                if not check_digit(name):
                    error.throw_syntax_error(arg)
                if name == ".":
                    if saw_dot:
                        error.throw_type_error("number", arg)
                    saw_dot = True
                elif name == '-':
                    if saw_minus:
                        error.throw_type_error("number", arg)
                    saw_minus = True
                innerlist.append(name)
        elif isinstance(arg, specialized_term_classes[".", 2]):
            innerlist += make_list(arg, numlist, saw_dot, saw_minus)
        else:
            error.throw_type_error("atom", arg)
    return numlist + innerlist


def check_digit(tocheck):
    return tocheck in "0123456789.-"


@expose_builtin("number_chars", unwrap_spec=["obj", "obj"])
def impl_number_chars(engine, heap, num, charlist):
    cons_cls = specialized_term_classes[".", 2]
    valid_list_type = isinstance(charlist, cons_cls) or isinstance(charlist, term.Var)

    if isinstance(num, term.Number) or isinstance(num, term.Float) or isinstance(num, term.BigInt):
        if not valid_list_type:
            error.throw_type_error("list", charlist)
        num_2_cons(num).unify(charlist, heap)
    elif isinstance(num, term.Var) and isinstance(charlist, cons_cls):
        cons_2_num(charlist).unify(num, heap)
    else:
        error.throw_type_error("number", num)
        
        
        

