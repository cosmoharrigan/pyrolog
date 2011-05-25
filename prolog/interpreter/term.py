import math
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter import error
from prolog.interpreter.signature import Signature
from pypy.rlib.objectmodel import we_are_translated, UnboxedValue
from pypy.rlib.objectmodel import compute_unique_id
from pypy.rlib.objectmodel import specialize
from pypy.rlib.debug import make_sure_not_resized
from pypy.rlib import jit
from pypy.tool.pairtype import extendabletype
from pypy.rlib.rbigint import rbigint

DEBUG = False

def debug_print(*args):
    if DEBUG and not we_are_translated():
        print " ".join([str(a) for a in args])


class PrologObject(object):
    __slots__ = ()
    __metaclass__ = extendabletype
    
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
    
    def cmp_standard_order(self, other, heap):
        raise NotImplementedError("abstract base class")

    def quick_unify_check(self, other):
        return True

class Var(PrologObject):
    TYPE_STANDARD_ORDER = 0
    __slots__ = ("binding", "created_after_choice_point")
    
    def __init__(self):
        self.binding = None
        self.created_after_choice_point = None
    
    @specialize.arg(3)
    @jit.unroll_safe
    def unify(self, other, heap, occurs_check=False):
        other = other.dereference(heap)
        next = self.binding
        while isinstance(next, Var):
            self = next
            next = next.binding
        if next is None:
            assert isinstance(self, Var)
            return self._unify_derefed(other, heap, occurs_check)
        else:
            assert isinstance(next, NonVar)
            if next is not other:
                if isinstance(other, NonVar):
                    self.setvalue(other, heap)
                next._unify_derefed(other, heap, occurs_check)

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
            if result is not next and heap is not None:
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
        self = self.dereference(heap)
        if isinstance(self, Var):
            res = memo.get(self)
            if res is not None:
                return res
            newvar = heap.newvar()
            memo.set(self, newvar)
            return newvar
        return self.copy(heap, memo)
    
    def enumerate_vars(self, memo):
        return memo.get(self)
    
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
        # XXX delete
        return self is other
    
    def eval_arithmetic(self, engine):
        self = self.dereference(None)
        if isinstance(self, Var):
            error.throw_instantiation_error()
        
        return self.eval_arithmetic(engine)
    
    @jit.dont_look_inside
    def cmp_standard_order(self, other, heap):
        assert isinstance(other, Var)
        return rcmp(compute_unique_id(self), compute_unique_id(other))

class AttMap(object):
    def __init__(self):
        self.indexes = {}
        self.other_maps = {}

    def get_index(self, attname):
        return self.indexes.get(attname, -1)

    def with_extra_attribute(self, attname):
        if attname not in self.other_maps:
            new_map = AttMap()
            new_map.last_name = attname
            new_map.indexes.update(self.indexes)
            new_map.indexes[attname] = len(self.indexes)
            self.other_maps[attname] = new_map
        return self.other_maps[attname]

class AttVar(Var):
    attmap = AttMap()

    def __init__(self):
        Var.__init__(self)
        self.value_list = []

    @specialize.arg(3)
    def _unify_derefed(self, other, heap, occurs_check=False):
        if isinstance(other, AttVar):
            if other is not self:
                self.setvalue(other, heap)
            return
        if isinstance(other, Var):
            return other._unify_derefed(self, heap, occurs_check)
        return self.setvalue(other, heap)

    def setvalue(self, value, heap):
        heap.add_hook(self)
        Var.setvalue(self, value, heap)

    def __repr__(self):
        attrs = []
        if self.value_list is not None:
            for key, index in self.attmap.indexes.iteritems():
                value = self.value_list[index]
                if value is not None:
                    attrs.append("%s=%s" % (key, value))
        return "AttVar(%s, %s)" % (self.binding, "[" + ", ".join(attrs) + "]")

    def copy(self, heap, memo):
        self = self.dereference(heap)
        if isinstance(self, AttVar):
            res = memo.get(self)
            if res is not None:
                return res
            newvar = heap.new_attvar()
            own_list = self.value_list
            newvar.attmap = self.attmap
            if own_list is None:
                newvar.value_list = None
            else:
                length = len(own_list)
                new_values = [None] * length
                for i in range(length):
                    if own_list[i] is None:
                        new_values[i] = None
                    else:
                        new_values[i] = own_list[i].copy(heap, memo)
                newvar.value_list = new_values

            memo.set(self, newvar)
            return newvar
        return self.copy(heap, memo)

    def add_attribute(self, attname, attribute):
        attmap = self.attmap
        index = attmap.get_index(attname)
        if index != -1:
            self.value_list[index] = attribute
            return
        self.attmap = attmap.with_extra_attribute(attname)
        self.value_list.append(attribute)

    def del_attribute(self, attname):
        index = self.attmap.get_index(attname)
        if self.value_list is not None:
            self.value_list[index] = None

    def get_attribute(self, attname):
        if self.value_list is None:
            return None, -1
        index = self.attmap.get_index(attname)
        if index == -1:
            return None, -1
        return self.value_list[index], index

    def reset_field(self, index, value):
        if self.value_list is None:
            self.value_list = [None] * (index + 1)
        while len(self.value_list) <= index:
            self.value_list.append(None)
        self.value_list[index] = value

    def invalidate_field(self, index):
        self.value_list[index] = None

    def get_attribute_index(self, attname):
        return self.attmap.get_index(attname)

    def is_empty(self):
        if self.value_list is None:
            return True
        for elem in self.value_list:
            if elem is not None:
                return False
        return True

class NumberedVar(PrologObject):
    _immutable_fields_ = ["num"]
    def __init__(self, index):
        self.num = index
    
    def copy_standardize_apart(self, heap, env):
        if self.num < 0:
            return heap.newvar()
        res = env[self.num]
        if res is None:
            res = env[self.num] = heap.newvar()
        return res
    
    def unify_and_standardize_apart(self, other, heap, env):
        if self.num < 0:
            return other
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
    __slots__ = ()

    def __init__(self):
        pass
    
    def name(self):
        return self.signature().name
        
    def signature(self):
        raise NotImplementedError("abstract base")
    
    def get_prolog_signature(self):
        return Callable.build("/", [Callable.build(self.name()),
                                    Number(self.argument_count())])
    def arguments(self):
        argcount = self.argument_count()
        result = [None] * argcount
        for i in range(argcount):
            result[i] = self.argument_at(i)
        return result
    
    def argument_at(self, i):
        raise NotImplementedError("abstract base")
    
    def argument_count(self):
        raise NotImplementedError("abstract base")
    
    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if (isinstance(other, Callable) and
                self.signature().eq(other.signature())):
            for i in range(self.argument_count()):
                self.argument_at(i).unify(other.argument_at(i), heap, occurs_check)
        else:
            raise UnificationFailed
    
    def copy_and_basic_unify(self, other, heap, env):
        if (isinstance(other, Callable) and
            self.signature().eq(other.signature())):
            for i in range(self.argument_count()):
                argself = self.argument_at(i)
                argother = other.argument_at(i)
                argself.unify_and_standardize_apart(argother, heap, env)
        else:
            raise UnificationFailed
    
    def copy(self, heap, memo):
        return self._copy_term(_term_copy, heap, memo)
    
    def copy_standardize_apart(self, heap, env):
        return self._copy_term(_term_copy_standardize_apart, heap, env)
    
    def enumerate_vars(self, memo):
        return self._copy_term(_term_enumerate_vars, None, memo)
    
    def getvalue(self, heap):
        return self._copy_term(_term_getvalue, heap)

    @specialize.arg(1)
    @jit.unroll_safe
    def _copy_term(self, copy_individual, heap, *extraargs):
        args = [None] * self.argument_count()
        newinstance = False
        i = 0
        while i < self.argument_count():
            arg = self.argument_at(i)
            cloned = copy_individual(arg, i, heap, *extraargs)
            newinstance = newinstance | (cloned is not arg)
            args[i] = cloned
            i += 1
        if newinstance:
            # XXX construct the right class directly
            return Callable.build(self.name(), args, self.signature(), heap=heap)
        else:
            return self
    
    def contains_var(self, var, heap):
        for arg in self.arguments():
            if arg.contains_var(var, heap):
                return True
        return False
    
    def cmp_standard_order(self, other, heap):
        assert isinstance(other, Callable)
        c = rcmp(self.argument_count(), other.argument_count())
        if c != 0:
            return c
        c = rcmp(self.name(), other.name())
        #print self.name()
        #print other.name()
        if c != 0:
            return c
        for i in range(self.argument_count()):
            a1 = self.argument_at(i).dereference(heap)
            a2 = other.argument_at(i).dereference(heap)
            c = cmp_standard_order(a1, a2, heap)
            if c != 0:
                return c
        return 0
    
    def eval_arithmetic(self, engine):
        from prolog.interpreter.arithmetic import get_arithmetic_function
        
        func = get_arithmetic_function(self.signature())
        if func is None:
            error.throw_type_error("evaluable", self.get_prolog_signature())
        return func(engine, self)
    
    @staticmethod
    @jit.unroll_safe
    def build(term_name, args=None, signature=None, heap=None, cache=True):
        if args is None:
            args = []
        if heap is not None:
            # perform variable shunting:
            # remove variables that are not needed because they are bound
            # already and cannot be backtracked
            for i in range(len(args)):
                arg = args[i]
                if (isinstance(arg, Var) and arg.binding is not None and
                        arg.created_after_choice_point is heap):
                    args[i] = arg.binding
        if len(args) == 0:
            if cache:
                return Atom.newatom(term_name)
            return Atom(term_name)
        else:
            if signature is None:
                if cache:
                    signature = Signature.getsignature(term_name, len(args))
                else:
                    signature = Signature(term_name, len(args))
            else:
                assert signature.numargs == len(args)
            assert isinstance(signature, Signature)

            cls = Callable._find_specialized_class(term_name, len(args))
            if cls is not None:
                return cls(term_name, args, signature)
            cls = Callable._find_specialized_class('Term', len(args))
            if cls is not None:
                return cls(term_name, args, signature)
            return Term(term_name, args, signature)
    
    @staticmethod
    @jit.purefunction
    def _find_specialized_class(term_name, numargs):
        return specialized_term_classes.get((term_name, numargs), None)

    def __repr__(self):
        return "%s(%s, %r)" % (self.__class__.__name__, self.name(),
                               self.arguments())

    @jit.unroll_safe
    def quick_unify_check(self, other):
        other = other.dereference(None)
        if isinstance(other, Var):
            return True
        if not isinstance(other, Callable):
            return False
        if not self.signature().eq(other.signature()):
            return False
        for i in range(self.argument_count()):
            if not self.argument_at(i).quick_unify_check(other.argument_at(i)):
                return False
        return True


class Atom(Callable):
    TYPE_STANDARD_ORDER = 1
    __slots__ = ('_name', '_signature')
    cache = {}
    _immutable_fields_ = ["_signature"]
    
    def __init__(self, name, signature=None):
        if signature is None:
            signature = Signature(name, 0)
        Callable.__init__(self)
        self._signature = signature
    
    def __str__(self):
        return self.name()
    
    def __repr__(self):
        return "Atom(%r)" % (self.name(),)
    
    @staticmethod
    def newatom(name):
        result = Atom.cache.get(name, None)
        if result is not None:
            return result
        signature = Signature.getsignature(name, 0)
        Atom.cache[name] = result = Atom(name, signature)
        return result
    
    def eval_arithmetic(self, engine):
        #XXX beautify that
        if self.name() == "pi":
            return Float.pi
        if self.name() == "e":
            return Float.e
        error.throw_type_error("evaluable", self.get_prolog_signature())
    
    def arguments(self):
        return []
    
    def argument_at(self, i):
        raise IndexError
    
    def argument_count(self):
        return 0
    
    def name(self):
        return self._signature.name
    
    def signature(self):
        return self._signature

class Numeric(NonVar):
    __slots__ = ()

class Number(Numeric): #, UnboxedValue):
    TYPE_STANDARD_ORDER = 3
    __slots__ = ("num", )
    _immutable_fields_ = ["num"]
    
    def __init__(self, num):
        assert isinstance(num, int)
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
    
    def cmp_standard_order(self, other, heap):
        # XXX looks a bit terrible
        if isinstance(other, Number):
            return rcmp(self.num, other.num)
        elif isinstance(other, Float):
            # return rcmp(self.num, other.floatval)
            return 1
        elif isinstance(other, BigInt):
            return bigint_cmp(rbigint.fromint(self.num), other.value)
        assert 0

    def quick_unify_check(self, other):
        other = other.dereference(None)
        if isinstance(other, Var):
            return True
        return isinstance(other, Number) and other.num == self.num


class BigInt(Numeric):
    TYPE_STANDARD_ORDER = 3
    __slots__ = ("value", )
    _immutable_fields_ = ["value"] # ?correct?
    # value is an instance of rbigint
    def __init__(self, value):
        self.value = value

    def basic_unify(self, other, heap, occurs_check=False):
        if isinstance(other, BigInt) and other.value.eq(self.value):
            return
        raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if isinstance(other, BigInt) and other.value.eq(self.value):
            return self
        raise UnificationFailed

    def __str__(self):
        return repr(self.value)

    def __repr__(self):
        return 'BigInt(rbigint(%s))' % self.value.str()

    def cmp_standard_order(self, other, heap):
        if isinstance(other, Number):
            return bigint_cmp(self.value, rbigint.fromint(other.num))
        elif isinstance(other, Float):
            return 1
        elif isinstance(other, BigInt):
            return bigint_cmp(self.value, other.value)
        assert 0

    
class Float(Numeric):
    TYPE_STANDARD_ORDER = 2
    _immutable_fields_ = ["floatval"]
    __slots__ = ("floatval", )
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
        return self
    
    def cmp_standard_order(self, other, heap):
        # XXX looks a bit terrible
        if isinstance(other, Number):
            # return rcmp(self.floatval, other.num)
            return -1
        elif isinstance(other, Float):
            return rcmp(self.floatval, other.floatval)
        elif isinstance(other, BigInt):
            return -1
        assert 0


Float.e = Float(math.e)
Float.pi = Float(math.pi)

# helper functions for various Term methods

def _term_copy(obj, i, heap, memo):
    return obj.copy(heap, memo)

def _term_copy_standardize_apart(obj, i, heap, env):
    return obj.copy_standardize_apart(heap, env)

def _term_enumerate_vars(obj, i, _, memo):
    return obj.enumerate_vars(memo)

def _term_getvalue(obj, i, heap):
    return obj.getvalue(heap)

def _term_unify_and_standardize_apart(obj, i, heap, other, memo):
    obj.unify_and_standardize_apart(other.argument_at(i), heap, memo)

class Term(Callable):
    TYPE_STANDARD_ORDER = 4
    _immutable_fields_ = ["_args[*]", "_name", "_signature"]
    __slots__ = ('_name', '_signature', '_args')
    
    def __init__(self, term_name, args, signature):
        assert signature.name == term_name
        self._args = make_sure_not_resized(args)
        self._signature = signature
        Callable.__init__(self)
    
    def __repr__(self):
        return "Term(%r, %r)" % (self.name(), self.arguments())
    
    def __str__(self):
        return "%s(%s)" % (self.name(), ", ".join([str(a) for a in self.arguments()]))
    
    def arguments(self):
        return self._args
    
    def argument_at(self, i):
        return self._args[i]
    
    def argument_count(self):
        return len(self._args)
    
    def signature(self):
        return self._signature

@specialize.argtype(0)
def rcmp(a, b): # RPython does not support cmp...
    if a == b:
        return 0
    if a < b:
        return -1
    return 1

def bigint_cmp(a, b):
    if a.eq(b):
        return 0
    if a.lt(b):
        return -1
    return 1

def cmp_standard_order(obj1, obj2, heap):
    c = rcmp(obj1.TYPE_STANDARD_ORDER, obj2.TYPE_STANDARD_ORDER)
    if c != 0:
        return c
    return obj1.cmp_standard_order(obj2, heap)

def generate_class(cname, fname, n_args):
    from pypy.rlib.unroll import unrolling_iterable
    arg_iter = unrolling_iterable(range(n_args))
    parent = callables['Abstract', n_args]
    assert parent is not None
    signature = Signature.getsignature(fname, n_args)
    
    class cls(parent):
        _immutable_ = True
        if n_args == 0:
            TYPE_STANDARD_ORDER = Atom.TYPE_STANDARD_ORDER
        else:
            TYPE_STANDARD_ORDER = Term.TYPE_STANDARD_ORDER
        
        def __init__(self, term_name, args, signature):
            parent._init_values(self, args)
            assert self.name() == term_name
            assert args is None or len(args) == n_args
                
        def name(self):
            return fname
        
        def signature(self):
            return signature

        def _make_new(self, name, signature):
            return cls(name, None, signature)
    
    cls.__name__ = cname
    return cls

def generate_abstract_class(n_args):
    from pypy.rlib.unroll import unrolling_iterable
    arg_iter = unrolling_iterable(range(n_args))
    class abstract_callable(Callable):
        _immutable_ = True
        def __init__(self, term_name, args, signature):
            raise NotImplementedError

        def _init_values(self, args):
            if args is None:
                return
            for x in arg_iter:
                setattr(self, 'val_%d' % x, args[x])

        def _make_new(self, name, signature):
            raise NotImplementedError("abstract base class")
        
        def arguments(self):
            result = [None] * n_args
            for x in arg_iter:
                result[x] = getattr(self, 'val_%d' % x)
            return result
        
        def argument_at(self, i):
            for x in arg_iter:
                if x == i:
                    return getattr(self, 'val_%d' % x)
            raise IndexError
        
        def argument_count(self):
            return n_args

        def quick_unify_check(self, other):
            other = other.dereference(None)
            if isinstance(other, Var):
                return True
            if not isinstance(other, Callable):
                return False
            if not self.signature().eq(other.signature()):
                return False
            if not isinstance(other, abstract_callable):
                return Callable.quick_unify_check(self, other)
            for x in arg_iter:
                a = getattr(self, 'val_%d' % x)
                b = getattr(other, 'val_%d' % x)
                if not a.quick_unify_check(b):
                    return False
            return True

        def copy_and_basic_unify(self, other, heap, env):
            if not isinstance(other, abstract_callable):
                return Callable.copy_and_basic_unify(self, other, heap, env)
            if self.signature().eq(other.signature()):
                for x in arg_iter:
                    a = getattr(self, 'val_%d' % x)
                    b = getattr(other, 'val_%d' % x)
                    a.unify_and_standardize_apart(b, heap, env)
            else:
                raise UnificationFailed

        @specialize.arg(3)
        @jit.dont_look_inside
        def basic_unify(self, other, heap, occurs_check=False):
            if not isinstance(other, abstract_callable):
                return Callable.basic_unify(self, other, heap, occurs_check)
            if self.signature().eq(other.signature()):
                for x in arg_iter:
                    a = getattr(self, 'val_%d' % x)
                    b = getattr(other, 'val_%d' % x)
                    a.unify(b, heap, occurs_check)
            else:
                raise UnificationFailed

        @specialize.arg(1)
        def _copy_term(self, copy_individual, heap, *extraargs):
            result = self._make_new(self.name(), self.signature())
            newinstance = False
            i = 0
            for i in arg_iter:
                arg = getattr(self, 'val_%d' % i)
                cloned = copy_individual(arg, i, heap, *extraargs)
                newinstance = newinstance | (cloned is not arg)
                setattr(result, 'val_%d' % i, cloned)
                i += 1
            if newinstance:
                # XXX what about the variable shunting in Callable.build
                return result
            else:
                return self
    
    abstract_callable.__name__ = 'Abstract'+str(n_args)
    return abstract_callable

def generate_generic_class(n_args):
    parent = callables['Abstract', n_args]
    assert parent is not None
    
    class generic_callable(parent):
        _immutable_ = True
        _immutable_fields_ = ["signature"]
        TYPE_STANDARD_ORDER = Term.TYPE_STANDARD_ORDER
        
        def __init__(self, term_name, args, signature):
            parent._init_values(self, args)
            self._signature = signature
            assert args is None or len(args) == n_args
            assert self.name() == term_name

        def _make_new(self, name, signature):
            return generic_callable(name, None, signature)
        
        def signature(self):
            return self._signature
        
    generic_callable.__name__ = 'Generic'+str(n_args)
    return generic_callable
    

specialized_term_classes = {}
callables = {}

for numargs in range(1, 10):
    callables['Abstract', numargs] = generate_abstract_class(numargs)

classes = [('Cons', '.', 2), ('Or', ';', 2), ('And', ',', 2)]
for cname, fname, numargs in classes:
    specialized_term_classes[fname, numargs] = generate_class(
                                                        cname, fname, numargs)

for numargs in range(1, 10):
    assert ('Term', numargs) not in specialized_term_classes
    specialized_term_classes['Term', numargs] = generate_generic_class(numargs)
