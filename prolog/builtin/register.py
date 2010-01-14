import py
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter import helper, term, error
from prolog.builtin import builtins, builtins_list

from pypy.rlib.objectmodel import we_are_translated

class Builtin(object):
    _immutable_ = True
    def __init__(self, function, name, numargs, signature):
        self.function = function
        self.name = name
        self.numargs = numargs
        self.signature = signature

    def call(self, engine, query, scont, fcont, heap):
        return self.function(engine, query, scont, fcont, heap)
        
    def _freeze_(self):
        return True

def expose_builtin(*args, **kwargs):
    def really_expose(func):
        return make_wrapper(func, *args, **kwargs)
    return really_expose

def make_wrapper(func, name, unwrap_spec=None, handles_continuation=False,
                   translatable=True):
    if isinstance(name, list):
        expose_as = name
        name = name[0]
    else:
        expose_as = [name]
    if not name.isalnum():
        name = func.func_name
    funcname = "wrap_%s_%s" % (name, len(unwrap_spec))
    code = ["def %s(engine, query, scont, fcont, heap):" % (funcname, )]
    if not translatable:
        code.append("    if we_are_translated():")
        code.append("        raise error.UncatchableError('%s does not work in translated version')" % (name, ))
    subargs = ["engine", "heap"]
    if len(unwrap_spec):
        code.append("    assert isinstance(query, term.Term)")
    else:
        code.append("    assert isinstance(query, term.Atom)")
    for i, spec in enumerate(unwrap_spec):
        varname = "var%s" % (i, )
        subargs.append(varname)
        if spec in ("obj", "callable", "int", "atom", "arithmetic"):
            code.append("    %s = query.args[%s].dereference(heap)" %
                        (varname, i))
        elif spec in ("concrete", "list"):
            code.append("    %s = query.args[%s].getvalue(heap)" %
                        (varname, i))
        if spec in ("int", "atom", "arithmetic", "list"):
            code.append(
                "    if isinstance(%s, term.Var):" % (varname,))
            code.append(
                "        error.throw_instantiation_error()")
        if spec == "obj":
            pass
        elif spec == "concrete":
            pass
        elif spec == "callable":
            code.append(
                "    if not isinstance(%s, term.Callable):" % (varname,))
            code.append(
                "        error.throw_type_error('callable', %s)" % (varname,))
        elif spec == "raw":
            code.append("    %s = query.args[%s]" % (varname, i))
        elif spec == "int":
            code.append("    %s = helper.unwrap_int(%s)" % (varname, varname))
        elif spec == "atom":
            code.append("    %s = helper.unwrap_atom(%s)" % (varname, varname))
        elif spec == "arithmetic":
            code.append("    %s = %s.eval_arithmetic(engine)" %
                        (varname, varname))
        elif spec == "list":
            code.append("    %s = helper.unwrap_list(%s)" % (varname, varname))
        else:
            assert 0, "not implemented " + spec
    if handles_continuation:
        subargs.append("scont")
        subargs.append("fcont")
    call = "    result = %s(%s)" % (func.func_name, ", ".join(subargs))
    code.append(call)
    if not handles_continuation:
        code.append("    return scont, fcont, heap")
    else:
        code.append("    return result")
    miniglobals = globals().copy()
    miniglobals[func.func_name] = func
    exec py.code.Source("\n".join(code)).compile() in miniglobals
    for name in expose_as:
        signature = "%s/%s" % (name, len(unwrap_spec))
        b = Builtin(miniglobals[funcname], funcname, len(unwrap_spec),
                    signature)
        builtins[signature] = b
        builtins_list.append((signature, b))
    return func
