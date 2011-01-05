import py
from prolog.interpreter import term, error
from prolog.builtin.register import expose_builtin
from prolog.interpreter.term import Callable
from prolog.interpreter.term import specialized_term_classes


def num_2_cons(num):
    numstr = str(num.num)[::-1]
    cons = Callable.build("[]")
    for digit in numstr:
        cons = Callable.build(".", [Callable.build(digit), cons])
    return cons


def cons_2_num(charlist):
    # a bit ugly
    numlist = make_list(charlist, [])
    print numlist
    if numlist[0] == '-' and len(numlist) == 1:
        error.throw_instantiation_error()
    return term.Number(int("".join(numlist)))


def make_list(cons, numlist):
    args = cons.arguments()
    innerlist = []
    for arg in args:
        if isinstance(arg, term.Atom):
            name = arg.name()
            if name != "[]":
                if not check_digit(name) and name != ".":
                    error.throw_syntax_error(arg)
                innerlist.append(name)
        elif isinstance(arg, specialized_term_classes['.', 2]):
            innerlist += make_list(arg, numlist)
        else:
            error.throw_type_error("Atom", arg)
    return numlist + innerlist
    

def extract_val(wrap, cons):
    val = wrap[:wrap.find("'")]
    if val != '.' and not check_digit(val):
        error.throw_syntax_error(cons)
    return val


def check_digit(tocheck):
    return tocheck in '0123456789'


@expose_builtin("number_chars", unwrap_spec=["obj", "obj"])
def impl_number_chars(engine, heap, num, charlist):
    cons_cls = specialized_term_classes[".", 2]
    valid_list_type = isinstance(charlist, cons_cls) or isinstance(charlist, term.Var)

    if isinstance(num, term.Number):
        print '!!'
        if not valid_list_type:
            error.throw_type_error("list", charlist)
        print num_2_cons(num)
        print charlist
        num_2_cons(num).unify(charlist, heap)
    elif isinstance(num, term.Var) and isinstance(charlist, cons_cls):
        cons_2_num(charlist).unify(num, heap)
    else:
        error.throw_type_error("number", num)
        
        
        

