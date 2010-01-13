import math
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter import error
from pypy.rlib.objectmodel import we_are_translated, UnboxedValue
from pypy.rlib.objectmodel import compute_unique_id
from pypy.rlib.objectmodel import specialize
from pypy.rlib.debug import make_sure_not_resized
from pypy.rlib import jit

DEBUG = False

def debug_print(*args):
    if DEBUG and not we_are_translated():
        print " ".join([str(a) for a in args])


class PrologObject(object):
    __slots__ = ()
    _immutable_ = True

    def getvalue(self, heap):
        return self

    def dereference(self, heap):
        raise NotImplementedError("abstract base class")

    def copy(self, heap, memo):
        raise NotImplementedError("abstract base class")

    def copy_standardize_apart(self, heap, env):
        raise NotImplementedError("abstract base class")

    def unify_and_standardize_apart(self, other, heap, env):
        raise NotImplementedError("abstract base class")

    def enumerate_vars(self, memo):
        raise NotImplementedError("abstract base class")

    @specialize.arg(3)
    def unify(self, other, heap, occurs_check=False):
        raise NotImplementedError("abstract base class")

    @specialize.arg(3)
    def _unify_derefed(self, other, heap, occurs_check=False):
        raise NotImplementedError("abstract base class")

    def contains_var(self, var, heap):
        return False

    def eval_arithmetic(self, engine):
        error.throw_type_error("evaluable", self)

class Var(PrologObject):
    TYPE_STANDARD_ORDER = 0

    created_after_choice_point = None

    def __init__(self):
        self.binding = None

    @specialize.arg(3)
    def unify(self, other, heap, occurs_check=False):
        other = other.dereference(heap)
        return self.dereference(heap)._unify_derefed(other, heap, occurs_check)

    @specialize.arg(3)
    def _unify_derefed(self, other, heap, occurs_check=False):
        if isinstance(other, Var) and other is self:
            pass
        elif occurs_check and other.contains_var(self, heap):
            raise UnificationFailed()
        else:
            self.setvalue(other, heap)

    def dereference(self, heap):
        next = self.binding
        if next is None:
            return self
        else:
            result = next.dereference(heap)
            if result is not next:
                # do path compression
                self.setvalue(result, heap)
            return result

    def getvalue(self, heap):
        res = self.dereference(heap)
        if not isinstance(res, Var):
            return res.getvalue(heap)
        return res

    def setvalue(self, value, heap):
        heap.add_trail(self)
        self.binding = value

    def copy(self, heap, memo):
        try:
            return memo[self]
        except KeyError:
            newvar = memo[self] = heap.newvar()
            return newvar

    def enumerate_vars(self, memo):
        if self in memo:
            return memo[self]
        result = NumberedVar(len(memo))
        memo[self] = result
        return result

    def contains_var(self, var, heap):
        self = self.dereference(heap)
        if self is var:
            return True
        if not isinstance(self, Var):
            return self.contains_var(var, heap)
        return False

    def __repr__(self):
        return "Var(%s)" % (self.binding, )


    def __eq__(self, other):
        # for testing
        return self is other

    def eval_arithmetic(self, engine):
        self = self.dereference(engine.heap)
        if isinstance(self, Var):
            error.throw_instantiation_error()

        return self.eval_arithmetic(engine)


class NumberedVar(PrologObject):
    _immutable_ = True
    def __init__(self, index):
        self.num = index

    def copy_standardize_apart(self, heap, env):
        res = env[self.num]
        if res is None:
            res = env[self.num] = heap.newvar()
        return res

    def unify_and_standardize_apart(self, other, heap, env):
        res = env[self.num]
        if res is None:
            env[self.num] = other
            return other
        res.unify(other, heap)
        return res

    def dereference(self, heap):
        return self

    def __repr__(self):
        return "NumberedVar(%s)" % (self.num, )


class NonVar(PrologObject):
    __slots__ = ()

    def dereference(self, heap):
        return self

    # needs to be overridden in non-atomic subclasses
    def copy(self, heap, memo):
        return self

    # needs to be overridden in non-atomic subclasses
    def copy_standardize_apart(self, heap, memo):
        return self

    @specialize.arg(3)
    def unify(self, other, heap, occurs_check=False):
        other = other.dereference(heap)
        return self._unify_derefed(other, heap, occurs_check)

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        raise NotImplementedError("abstract base class")

    @specialize.arg(3)
    def _unify_derefed(self, other, heap, occurs_check=False):
        if isinstance(other, Var):
            other._unify_derefed(self, heap, occurs_check)
        else:
            self.basic_unify(other, heap, occurs_check)

    def unify_and_standardize_apart(self, other, heap, env):
        other = other.dereference(heap)
        if isinstance(other, Var):
            copy = self.copy_standardize_apart(heap, env)
            other._unify_derefed(copy, heap)
            return copy
        else:
            return self.copy_and_basic_unify(other, heap, env)

    def copy_and_basic_unify(self, other, heap, env):
        raise NotImplementedError("abstract base class")

    def enumerate_vars(self, memo):
        return self

class Callable(NonVar):
    __slots__ = ("name", "signature")
    _immutable_ = True
    name = ""
    signature = ""

    def get_prolog_signature(self):
        raise NotImplementedError("abstract base")


class Atom(Callable):
    TYPE_STANDARD_ORDER = 1

    cache = {}
    _immutable_ = True

    def __init__(self, name):
        self.name = name
        self.signature = self.name + "/0"

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Atom(%r)" % (self.name,)

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, Atom) and (self is other or
                                        other.name == self.name):
            return
        raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if isinstance(other, Atom) and (self is other or
                                        other.name == self.name):
            return self
        else:
            raise UnificationFailed

    def get_prolog_signature(self):
        return Term("/", [self, NUMBER_0])

    @staticmethod
    def newatom(name):
        result = Atom.cache.get(name, None)
        if result is not None:
            return result
        Atom.cache[name] = result = Atom(name)
        return result

    def eval_arithmetic(self, engine):
        #XXX beautify that
        if self.name == "pi":
            return Float.pi
        if self.name == "e":
            return Float.e
        error.throw_type_error("evaluable", self.get_prolog_signature())


class Number(NonVar): #, UnboxedValue):
    TYPE_STANDARD_ORDER = 2
    _immutable_ = True
    __slots__ = ("num", )

    def __init__(self, num):
        self.num = num

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, Number) and other.num == self.num:
            return
        raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if isinstance(other, Number) and other.num == self.num:
            return self
        else:
            raise UnificationFailed

    def __str__(self):
        return repr(self.num)

    def __repr__(self):
        return "Number(%r)" % (self.num, )

    def eval_arithmetic(self, engine):
        return self

NUMBER_0 = Number(0)

class Float(NonVar):
    TYPE_STANDARD_ORDER = 2
    _immutable_ = True
    def __init__(self, floatval):
        self.floatval = floatval

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, Float) and other.floatval == self.floatval:
            return
        raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if isinstance(other, Float) and other.floatval == self.floatval:
            return self
        else:
            raise UnificationFailed

    def __str__(self):
        return repr(self.floatval)

    def __repr__(self):
        return "Float(%r)" % (self.floatval, )

    def eval_arithmetic(self, engine):
        from prolog.interpreter.arithmetic import norm_float
        return norm_float(self)

Float.e = Float(math.e)
Float.pi = Float(math.pi)


class BlackBox(NonVar):
    # meant to be subclassed
    TYPE_STANDARD_ORDER = 4
    def __init__(self):
        pass

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if self is other:
            return
        raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, memo):
        if self is other:
            return self
        else:
            raise UnificationFailed


# helper functions for various Term methods

def _term_copy(obj, i, heap, memo):
    return obj.copy(heap, memo)

def _term_copy_standardize_apart(obj, i, heap, env):
    return obj.copy_standardize_apart(heap, env)

def _term_enumerate_vars(obj, i, memo):
    return obj.enumerate_vars(memo)

def _term_getvalue(obj, i, heap):
    return obj.getvalue(heap)

def _term_unify_and_standardize_apart(obj, i, other, heap, memo):
    obj.unify_and_standardize_apart(other.args[i], heap, memo)

class Term(Callable):
    TYPE_STANDARD_ORDER = 3
    _immutable_ = True
    _immutable_fields_ = ["args[*]"]

    def __init__(self, name, args, signature=None):
        self.name = name
        self.args = make_sure_not_resized(args)
        if signature is None:
            self.signature = name + "/" + str(len(args))
        else:
            self.signature = signature

    def __repr__(self):
        return "Term(%r, %r)" % (self.name, self.args)

    def __str__(self):
        return "%s(%s)" % (self.name, ", ".join([str(a) for a in self.args]))

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if (isinstance(other, Term) and
            self.name == other.name and
            len(self.args) == len(other.args)):
            for i in range(len(self.args)):
                self.args[i].unify(other.args[i], heap, occurs_check)
        else:
            raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if (isinstance(other, Term) and
                self.signature == other.signature):
            return self._copy_term(_term_unify_and_standardize_apart,
                                   other, heap, env)
        else:
            raise UnificationFailed

    def copy(self, heap, memo):
        return self._copy_term(_term_copy, heap, memo)

    def copy_standardize_apart(self, heap, env):
        return self._copy_term(_term_copy_standardize_apart, heap, env)

    def enumerate_vars(self, memo):
        return self._copy_term(_term_enumerate_vars, memo)

    def getvalue(self, heap):
        return self._copy_term(_term_getvalue, heap)

    @specialize.arg(1)
    @jit.unroll_safe
    def _copy_term(self, copy_individual, *extraargs):
        args = [None] * len(self.args)
        newinstance = False
        i = 0
        while i < len(self.args):
            arg = self.args[i]
            cloned = copy_individual(arg, i, *extraargs)
            newinstance = newinstance or cloned is not arg
            args[i] = cloned
            i += 1
        if newinstance:
            return Term(self.name, args, self.signature)
        else:
            return self

    def get_prolog_signature(self):
        return Term("/", [Atom.newatom(self.name), Number(len(self.args))])
    
    def contains_var(self, var, heap):
        for arg in self.args:
            if arg.contains_var(var, heap):
                return True
        return False
        
    def eval_arithmetic(self, engine):
        from prolog.interpreter.arithmetic import get_arithmetic_function

        func = get_arithmetic_function(self.signature)
        if func is None:
            error.throw_type_error("evaluable", self.get_prolog_signature())
        return func(engine, self)


@specialize.argtype(0)
def rcmp(a, b): # RPython does not support cmp...
    if a == b:
        return 0
    if a < b:
        return -1
    return 1

def cmp_standard_order(obj1, obj2, heap):
    c = rcmp(obj1.TYPE_STANDARD_ORDER, obj2.TYPE_STANDARD_ORDER)
    if c != 0:
        return c
    if isinstance(obj1, Var):
        assert isinstance(obj2, Var)
        return rcmp(compute_unique_id(obj1), compute_unique_id(obj2))
    if isinstance(obj1, Atom):
        assert isinstance(obj2, Atom)
        return rcmp(obj1.name, obj2.name)
    if isinstance(obj1, Term):
        assert isinstance(obj2, Term)
        c = rcmp(len(obj1.args), len(obj2.args))
        if c != 0:
            return c
        c = rcmp(obj1.name, obj2.name)
        if c != 0:
            return c
        for i in range(len(obj1.args)):
            a1 = obj1.args[i].dereference(heap)
            a2 = obj2.args[i].dereference(heap)
            c = cmp_standard_order(a1, a2, heap)
            if c != 0:
                return c
        return 0
    # XXX hum
    if isinstance(obj1, Number):
        if isinstance(obj2, Number):
            return rcmp(obj1.num, obj2.num)
        elif isinstance(obj2, Float):
            return rcmp(obj1.num, obj2.floatval)
    if isinstance(obj1, Float):
        if isinstance(obj2, Number):
            return rcmp(obj1.floatval, obj2.num)
        elif isinstance(obj2, Float):
            return rcmp(obj1.floatval, obj2.floatval)
    assert 0
