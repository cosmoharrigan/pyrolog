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

    def cmp_standard_order(self, other, heap):
        raise NotImplementedError("abstract base class")
        
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
        # XXX delete
        return self is other

    def eval_arithmetic(self, engine):
        self = self.dereference(engine.heap)
        if isinstance(self, Var):
            error.throw_instantiation_error()

        return self.eval_arithmetic(engine)

    @jit.dont_look_inside
    def cmp_standard_order(self, other, heap):
        assert isinstance(other, Var)
        return rcmp(compute_unique_id(self), compute_unique_id(other))
        


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
    _immutable_ = True
    __slots__ = ()
    
    def name(self):
        raise NotImplementedError("abstract base")
        
    def signature(self):
        raise NotImplementedError("abstract base")
        
    def get_prolog_signature(self):
        return Term("/", [Callable.build(self.name()),
                                                Number(self.argument_count())])        
    def arguments(self):
        raise NotImplementedError("abstract base")
        
    def argument_at(self, i):
        raise NotImplementedError("abstract base")

    def argument_count(self):
        raise NotImplementedError("abstract base")

    @specialize.arg(3)
    def basic_unify(self, other, heap, occurs_check=False):
        if (isinstance(other, Callable) and
                self.signature() == other.signature()):
            for i in range(self.argument_count()):
                self.argument_at(i).unify(other.argument_at(i), heap, occurs_check)
        else:
            raise UnificationFailed

    def copy_and_basic_unify(self, other, heap, env):
        if (isinstance(other, Callable) and 
            self.signature() == other.signature()):
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
        args = [None] * self.argument_count()
        newinstance = False
        i = 0
        while i < self.argument_count():
            arg = self.argument_at(i)
            cloned = copy_individual(arg, i, *extraargs)
            newinstance = newinstance or cloned is not arg
            args[i] = cloned
            i += 1
        if newinstance:
            # XXX construct the right class directly
            return Callable.build(self.name(), args, self.signature())
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
    def build(term_name, args=None, signature=None):
        if args is None:
            args = []
        if len(args) == 0:
            return Atom.newatom(term_name)
        else:
            cls = Callable._find_specialized_class(term_name, len(args))
            if cls is not None:
                return cls(args)
            cls = Callable._find_specialized_class('Term', len(args))
            if cls is not None:
                print 'Using specialized term for %s/%d' % (term_name, len(args))
                return cls(term_name, args)
            return Term(term_name, args, signature)

    @staticmethod
    @jit.purefunction
    def _find_specialized_class(term_name, numargs):
        return specialized_term_classes.get((term_name, numargs), None)


        
class Atom(Callable):
    TYPE_STANDARD_ORDER = 1
    # __slots__ = ('_name', '_signature')
    cache = {}
    _immutable_ = True

    def __init__(self, name):
        self._name = name
        self._signature = self._name + "/0"

    def __str__(self):
        return self.name()

    def __repr__(self):
        return "Atom(%r)" % (self.name(),)

    @staticmethod
    def newatom(name):
        result = Atom.cache.get(name, None)
        if result is not None:
            return result
        Atom.cache[name] = result = Atom(name)
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
        return self._name
        
    def signature(self):
        return self._signature

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

    def cmp_standard_order(self, other, heap):
        # XXX looks a bit terrible
        if isinstance(other, Number):
            return rcmp(self.num, other.num)
        elif isinstance(other, Float):
            return rcmp(self.num, other.floatval)
        assert 0
        
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
        
    def cmp_standard_order(self, other, heap):
        # XXX looks a bit terrible
        if isinstance(other, Number):
            return rcmp(self.floatval, other.num)
        elif isinstance(other, Float):
            return rcmp(self.floatval, other.floatval)
        assert 0
        
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
    obj.unify_and_standardize_apart(other.argument_at(i), heap, memo)

class Term(Callable):
    TYPE_STANDARD_ORDER = 3
    _immutable_ = True
    _immutable_fields_ = ["_args[*]"]
    __slots__ = ('_name', '_signature', '_args')
    
    def __init__(self, term_name, args, signature=None):
        self._name = term_name
        self._args = make_sure_not_resized(args)
        if signature is None:
            self._signature = term_name + "/" + str(len(args))
        else:
            self._signature = signature
                    
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
        
    def name(self):
        return self._name
        
    def signature(self):
        return self._signature
        
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
    return obj1.cmp_standard_order(obj2, heap)

def generate_class(cname, fname, n_args):
    from pypy.rlib.unroll import unrolling_iterable
    arg_iter = unrolling_iterable(range(n_args))
    signature = fname + '/' + str(n_args)
    class cls(Callable):
        _immutable_ = True
        if n_args == 0:
            TYPE_STANDARD_ORDER = Atom.TYPE_STANDARD_ORDER
        else:
            TYPE_STANDARD_ORDER = Term.TYPE_STANDARD_ORDER
            
        def __init__(self, args):
            assert len(args) == n_args
            for x in arg_iter:
                setattr(self, 'val_%d' % x, args[x])
                
        def name(self):
            return fname
        
        def signature(self):
            return signature
        
        def arguments(self):
            result = [None] * n_args
            for x in arg_iter:
                result[x] = getattr(self, 'val_%d' % x)
            return result

        def argument_at(self, i):
            for x in arg_iter:
                if x == i:
                    return getattr(self, 'val_%d' % x)

        def argument_count(self):
            return n_args
            
    cls.__name__ = cname
    return cls

def generate_term_class(n_args):
    from pypy.rlib.unroll import unrolling_iterable
    arg_iter = unrolling_iterable(range(n_args))
    class term_cls(Callable):
        # _immutable_ = True
        TYPE_STANDARD_ORDER = Term.TYPE_STANDARD_ORDER

        def __init__(self, term_name, args):
            self._name = term_name
            self._signature = term_name+"/"+str(n_args)
            assert len(args) == n_args
            for x in arg_iter:
                setattr(self, 'val_%d' % x, args[x])

        def name(self):
            return self._name

        def signature(self):
            return self._signature

        def arguments(self):
            result = [None] * n_args
            for x in arg_iter:
                result[x] = getattr(self, 'val_%d' % x)
            return result

        def argument_at(self, i):
            for x in arg_iter:
                if x == i:
                    return getattr(self, 'val_%d' % x)

        def argument_count(self):
            return n_args
            
        def __str__(self):
            return "Term%d(%s, %r)" % (n_args, self.name(), self.arguments())
        __repr__ = __str__
    term_cls.__name__ = 'Term'+str(n_args)
    return term_cls
    
specialized_term_classes = {}
classes = [('Cons', '.', 2), ('Or', ';', 2), ('And', ',', 2), ('Cut', '!', 0), ('Nil', '[]', 0)]
for cname, fname, numargs in classes:
    specialized_term_classes[fname, numargs] = generate_class(cname, fname, numargs)
for numargs in range(1,4):
    specialized_term_classes['Term', numargs] = generate_term_class(numargs)
