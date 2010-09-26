import py
import math
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter import helper, term, error
from prolog.interpreter.signature import Signature
from prolog.interpreter.error import UnificationFailed
from pypy.rlib.rarithmetic import intmask
from pypy.rlib.unroll import unrolling_iterable
from pypy.rlib import jit, rarithmetic
from pypy.rlib.rbigint import rbigint

Signature.register_extr_attr("arithmetic")

class CodeCollector(object):
    def __init__(self):
        self.code = []
        self.blocks = []

    def emit(self, line):
        for line in line.split("\n"):
            self.code.append(" " * (4 * len(self.blocks)) + line)

    def start_block(self, blockstarter):
        assert blockstarter.endswith(":")
        self.emit(blockstarter)
        self.blocks.append(blockstarter)

    def end_block(self, starterpart=""):
        block = self.blocks.pop()
        assert starterpart in block, "ended wrong block %s with %s" % (
            block, starterpart)

    def tostring(self):
        assert not self.blocks
        return "\n".join(self.code)

def wrap_builtin_operation(name, pattern, unwrap_spec, can_overflow, intversion):
    """
    code = CodeCollector()
    code.start_block("def prolog_%s(engine, query):" % name)
    for i, spec in enumerate(unwrap_spec):
        varname = "var%s" % (i, )
        code.emit("%s = eval_arithmetic(engine, query.argument_at(%s))" %
                  (varname, i))
    for i, spec in enumerate(unwrap_spec):
        varname = "var%s" % (i, )
        if spec == "int":
            code.start_block(
                "if not isinstance(%s, term.Number):" % (varname, ))
            code.emit("error.throw_type_error('int', %s)" % (varname, ))
            code.end_block("if")
    if "expr" in unwrap_spec and intversion:
        # check whether all arguments are ints
        for i, spec in enumerate(unwrap_spec):
            varname = "var%s" % (i, )
            if spec == "int":
                continue
            code.start_block(
                "if isinstance(%s, term.Number):" % (varname, ))
            code.emit("v%s = var%s.num" % (i, i))
        code.emit("return term.Number(int(%s))" % (pattern, ))
        for i, spec in enumerate(unwrap_spec):
            if spec == "int":
                continue
            code.end_block("if")
    
    #general case in an extra function
    args = ", ".join(["var%s" % i for i in range(len(unwrap_spec))])
    code.emit("return general_%s(%s)" % (name, args))
    code.end_block("def")
    code.start_block("def general_%s(%s):" % (name, args))
    for i, spec in enumerate(unwrap_spec):
        varname = "var%s" % (i, )
        code.emit("v%s = 0" % (i, ))
        code.start_block("if isinstance(%s, term.Number):" % (varname, ))
        code.emit("v%s = %s.num" % (i, varname))
        code.end_block("if")
        expected = 'int'
        if spec == "expr":
            code.start_block("elif isinstance(%s, term.Float):" % (varname, ))
            code.emit("v%s = %s.floatval" % (i, varname))
            code.end_block("elif")
            expected = 'float'
        code.start_block("else:")
        code.emit("error.throw_type_error('%s', %s)" % (expected, varname, ))
        code.end_block("else")
    code.emit("return norm_float(term.Float(%s))" % pattern)
    code.end_block("def")
    miniglobals = globals().copy()
    """
    #print "___________ CODE _______________"
    print 'NAME =', name
    #print code.tostring()
    #print "________________________________"
    #### !!! ####
    fcode = CodeCollector()
    fcode.start_block('def prolog_%s(engine, query):' % name)
    for i, _ in enumerate(unwrap_spec):
        fcode.emit('var%s = eval_arithmetic(engine, query.argument_at(%s))' % (i, i))
    if len(unwrap_spec) == 1:
        fcode.emit('return var0.arith_%s()' % name)
    elif len(unwrap_spec) == 2:
        fcode.emit('return var0.arith_%s(var1)' % name)
    fcode.end_block('def')
    miniglobals = globals().copy()
    exec py.code.Source(fcode.tostring()).compile() in miniglobals
    result = miniglobals['prolog_' + name]
    return result

    #print '=== F C O D E ===\n', fcode.tostring(), '\n============'
    #############
    """
    exec py.code.Source(code.tostring()).compile() in miniglobals
    result = miniglobals["prolog_" + name]
    return result
    """
wrap_builtin_operation._annspecialcase_ = 'specialize:memo'

def eval_arithmetic(engine, query):
    return query.eval_arithmetic(engine)

def norm_float(obj):
    v = obj.floatval
    if v == int(v):
        return term.Number(int(v))
    else:
        return obj

simple_functions = [
    ("+",                     ["expr", "expr"], "v0 + v1", True, True),
    ("-",                     ["expr", "expr"], "v0 - v1", True, True),
    ("*",                     ["expr", "expr"], "v0 * v1", True, True),
    ("//",                    ["int",  "int"],  "v0 / v1", True, False),
    
    (">>",                    ["int", "int"],   "v0 >> v1", False, False),
    ("<<",                    ["int", "int"],   "intmask(v0 << v1)", False,
                                                                     False),
    ("\\/",                   ["int", "int"],   "v0 | v1", False, False),
    ("/\\",                   ["int", "int"],   "v0 & v1", False, False),
    ("xor",                   ["int", "int"],   "v0 ^ v1", False, False),
    ("mod",                   ["int", "int"],   "v0 % v1", False, False),
    ("\\",                    ["int"],          "~v0", False, False),
    ("abs",                   ["expr"],         "abs(v0)", True, True),
    ("max",                   ["expr", "expr"], "max(v0, v1)", False, True),
    ("min",                   ["expr", "expr"], "min(v0, v1)", False, True),
    ("round",                 ["expr"],         "int(v0 + 0.5)", False, False),
    ("floor",                 ["expr"],         "math.floor(v0)", False, False), #XXX
    ("ceiling",               ["expr"],         "math.ceil(v0)", False, False), #XXX
    ("float_fractional_part", ["expr"],         "v0 - int(v0)", False, False), #XXX
    ("float_integer_part",    ["expr"],         "int(v0)", False, True),
]

for prolog_name, unwrap_spec, pattern, overflow, intversion in simple_functions:
    # the name is purely for flowgraph viewing reasons
    if prolog_name.replace("_", "").isalnum():
        name = prolog_name
    else:
        import unicodedata
        name = "".join([unicodedata.name(unicode(c)).replace(" ", "_").replace("-", "").lower() for c in prolog_name])
    """
    print '____________________________'
    print 'prolog_name =', prolog_name
    print 'pattern = ', pattern
    print 'unwrap_spec =', unwrap_spec
    print '____________________________'
    """

    f = wrap_builtin_operation(name, pattern, unwrap_spec, overflow,
                               intversion)
    
    signature = Signature.getsignature(prolog_name, len(unwrap_spec))
    signature.set_extra("arithmetic", f)

@jit.purefunction
def get_arithmetic_function(signature):
    return signature.get_extra("arithmetic")


class __extend__(term.Number):
    # ------------------ addition ------------------ 
    def arith_plus_sign(self, other):
        return other.arith_add_number(self.num)

    def arith_add_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num + self.num)
        except OverflowError:
            return self.arith_add_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_add_bigint(self, other_value):
        return term.BigInt(other_value.add(rbigint.fromint(self.num)))

    def arith_add_float(self, other_float):
        return term.Float(other_float + float(self.num))

    # ------------------ subtraction ------------------ 
    def arith_hyphenminus(self, other):
        return other.arith_sub_number(self.num)

    def arith_sub_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num - self.num)
        except OverflowError:
            return self.arith_sub_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_sub_bigint(self, other_value):
        return term.BigInt(other_value.sub(rbigint.fromint(self.num)))

    def arith_sub_float(self, other_float):
        return term.Float(other_float - float(self.num))

    # ------------------ multiplication ------------------ 
    def arith_asterisk(self, other):
        return other.arith_mul_number(self.num)

    def arith_mul_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num * self.num)
        except OverflowError:
            return self.arith_mul_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_mul_bigint(self, other_value):
        return term.BigInt(other_value.mul(rbigint.fromint(self.num)))

    def arith_mul_float(self, other_float):
        return term.Float(other_float * float(self.num))

    # ------------------ division ------------------ 
    def arith_solidussolidus(self, other):
        return other.arith_div_number(self.num)

    def arith_div_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num / self.num)
        except OverflowError:
            return self.arith_div_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_div_bigint(self, other_value):
        return term.BigInt(other_value.div(rbigint.fromint(self.num)))

    def arith_div_float(self, other_float):
        return term.Float(other_float / float(self.num))

    # ------------------ power ------------------ 
    def arith_pow(self, other):
        return other.arith_pow_number(self.num)

    def arith_pow_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num ** self.num)
        except OverflowError:
            return self.arith_pow_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_pow_bigint(self, other_value):
        return term.BigInt(other_value.pow(rbigint.fromint(self.num)))

    def arith_pow_float(self, other_float):
        return term.Float(other_float ** float(self.num))

    # ------------------ shift right ------------------ 
    def arith_greaterthan_signgreaterthan_sign(self, other):
        return other.arith_shr_number(self.num)

    def arith_shr_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num >> self.num)
        except OverflowError:
            return self.arith_shr_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_shr_bigint(self, other_value):
        return term.BigInt(other_value.rshift(self.num))

    # ------------------ shift left ------------------ 
    def arith_lessthan_signlessthan_sign(self, other):
        return other.arith_shl_number(self.num)

    def arith_shl_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(intmask(other_num << self.num))
        except OverflowError:
            return self.arith_shl_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_shl_bigint(self, other_value):
        return term.BigInt(other_value.lshift(self.num))

    # ------------------ or ------------------ 
    def arith_reverse_solidussolidus(self, other):
        return other.arith_or_number(self.num)

    def arith_or_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num | self.num)
        except OverflowError:
            return self.arith_or_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_or_bigint(self, other_value):
        return term.BigInt(rbigint.fromint(self.num).or_(other_value))

    # ------------------ and ------------------ 
    def arith_solidusreverse_solidus(self, other):
        return other.arith_and_number(self.num)

    def arith_and_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num & self.num)
        except OverflowError:
            return self.arith_and_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_and_bigint(self, other_value):
        return term.BigInt(rbigint.fromint(self.num).and_(other_value))

    # ------------------ xor ------------------ 
    def arith_xor(self, other):
        return other.arith_xor_number(self.num)

    def arith_xor_number(self, other_num):
        try:
            res = rarithmetic.ovfcheck(other_num ^ self.num)
        except OverflowError:
            return self.arith_xor_bigint(rbigint.fromint(other_num))
        return term.Number(res)

    def arith_xor_bigint(self, other_value):
        return term.BigInt(rbigint.fromint(self.num).xor(other_value))

    # ------------------ mod ------------------ 
    def arith_mod(self, other):
        return other.arith_mod_number(self.num)

    def arith_mod_number(self, other_num):
        return term.Number(other_num % self.num)

    def arith_mod_bigint(self, other_value):
        return term.BigInt(other_value.mod(rbigint.fromint(self.num)))

    # ------------------ inversion ------------------
    def arith_reverse_solidus(self):
        try:
            val = rarithmetic.ovfcheck(~self.num)
        except OverflowError:
            return term.BigInt(rbigint.fromint(self.num).invert())
        return term.Number(val)


    # ------------------ abs ------------------
    def arith_abs(self):
        try:
            val = rarithmetic.ovfcheck(abs(self.num))
        except OverflowError:
            return term.BigInt(rbigint.fromint(self.num).abs())
        return term.Number(val)

    # ------------------ max ------------------
    def arith_max(self, other):
        return other.arith_max_number(self.num)

    def arith_max_number(self, other_num):
        return term.Number(max(other_num, self.num))

    def arith_max_bigint(self, other_value):
        self_value = rbigint.fromint(self.num)
        if self_value.lt(other_value):
            return term.BigInt(other_value)
        return term.BigInt(self_value)

    def arith_max_float(self, other_float):
        return term.Float(max(other_float, float(self.num)))

    # ------------------ min ------------------
    def arith_min(self, other):
        return other.arith_min_number(self.num)

    def arith_min_number(self, other_num):
        return term.Number(min(other_num, self.num))

    def arith_min_bigint(self, other_value):
        self_value = rbigint.fromint(self.num)
        if self_value.lt(other_value):
            return term.BigInt(self_value)
        return term.BigInt(other_value)

    def arith_min_float(self, other_float):
        return term.Float(min(other_float, float(self.num)))

    # ------------------ miscellanous ------------------
    def arith_round(self):
        return self

    def arith_floor(self):
        return self

    def arith_ceiling(self):
        return self

    def arith_float_fractional_part(self):
        return term.Number(0)

    def arith_float_integer_part(self):
        return self


class __extend__(term.Float):    
    # ------------------ addition ------------------ 
    def arith_plus_sign(self, other):
        return other.arith_add_float(self.floatval)

    def arith_add_number(self, other_num):
        return term.Float(float(other_num) + self.floatval)

    def arith_add_bigint(self, other_value):
        return term.Float(other_value.tofloat() + self.floatval)

    def arith_add_float(self, other_float):
        """
        if sum == int(sum):
            try:
                sum = rarithmetic.ovfcheck(other_float + self.float)
                if int(sum) == sum:
                    return term.Number(int(sum))
            except OverflowError:
                
        """        
        return term.Float(other_float + self.floatval)

    # ------------------ subtraction ------------------ 
    def arith_hyphenminus(self, other):
        return other.arith_sub_float(self.floatval)

    def arith_sub_number(self, other_num):
        return term.Float(float(other_num) - self.floatval)

    def arith_sub_bigint(self, other_value):
        return term.Float(other_value.tofloat() - self.floatval)

    def arith_sub_float(self, other_float):
        return term.Float(other_float - self.floatval)

    # ------------------ multiplication ------------------ 
    def arith_asterisk(self, other):
        return other.arith_mul_float(self.floatval)

    def arith_mul_number(self, other_num):
        return term.Float(float(other_num) * self.floatval)

    def arith_mul_bigint(self, other_value):
        return term.Float(other_value.tofloat() * self.floatval)

    def arith_mul_float(self, other_float):
        return term.Float(other_float * self.floatval)

    # ------------------ division ------------------ 
    def arith_solidussolidus(self, other):
        return other.arith_div_float(self.floatval)

    def arith_div_number(self, other_num):
        return term.Float(float(other_num) / self.floatval)

    def arith_div_bigint(self, other_value):
        return term.Float(other_value.tofloat() / self.floatval)

    def arith_div_float(self, other_float):
        return term.Float(other_float / self.floatval)

    # ------------------ power ------------------ 
    def arith_pow(self, other):
        return other.arith_pow_float(self.floatval)

    def arith_pow_number(self, other_num):
        return term.Float(float(other_num) ** self.floatval)

    def arith_pow_bigint(self, other_value):
        return term.Float(other_value.tofloat() ** self.floatval)

    def arith_pow_float(self, other_float):
        return term.Float(other_float ** self.floatval)

    # ------------------ abs ------------------ 
    def arith_abs(self):
        return term.Float(abs(self.floatval))

    # ------------------ max ------------------ 
    def arith_max(self, other):
        return other.arith_max_float(self.floatval)

    def arith_max_number(self, other_num):
        return term.Float(max(float(other_num), self.floatval))

    def arith_max_bigint(self, other_value):
        return term.Float(max(other_value.tofloat(), self.floatval))

    def arith_max_float(self, other_float):
        return term.Float(max(other_float, self.floatval))
    
    # ------------------ min ------------------ 
    def arith_min(self, other):
        return other.arith_min_float(self.floatval)

    def arith_min_number(self, other_num):
        return term.Float(min(float(other_num), self.floatval))

    def arith_min_bigint(self, other_value):
        return term.Float(min(other_value.tofloat(), self.floatval))

    def arith_min_float(self, other_float):
        return term.Float(min(other_float, self.floatval))

    # ------------------ miscellanous ------------------
    def arith_round(self):
        return term.Number(round(self.floatval)) # XXX

    def arith_floor(self):
        return term.Float(math.floor(self.floatval))

    def arith_ceiling(self):
        return term.Float(math.ceil(self.floatval))

    def arith_float_fractional_part(self):
        return term.Float(self.floatval - int(self.floatval))

    def arith_float_integer_part(self):
        return term.Float(int(self.floatval))


class __extend__(term.BigInt):
    # ------------------ addition ------------------ 
    def arith_plus_sign(self, other):
        return other.arith_add_bigint(self.value)

    def arith_add_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).add(self.value))

    def arith_add_bigint(self, other_value):
        return term.BigInt(other_value.add(self.value))

    def arith_add_float(self, other_float):
        return term.Float(other_float + self.value.tofloat())

    # ------------------ subtraction ------------------ 
    def arith_hyphenminus(self, other):
        return other.arith_sub_bigint(self.value)

    def arith_sub_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).sub(self.value))

    def arith_sub_bigint(self, other_value):
        return term.BigInt(other_value.sub(self.value))

    def arith_sub_float(self, other_float):
        return term.Float(other_float - self.value.tofloat())

    # ------------------ multiplication ------------------ 
    def arith_asterisk(self, other):
        return other.arith_mul_bigint(self.value)

    def arith_mul_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).mul(self.value))

    def arith_mul_bigint(self, other_value):
        return term.BigInt(other_value.mul(self.value))

    def arith_mul_float(self, other_float):
        return term.Float(other_float * self.value.tofloat())

    # ------------------ division ------------------ 
    def arith_solidussolidus(self, other):
        return other.arith_div_bigint(self.value)

    def arith_div_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).div(self.value))

    def arith_div_bigint(self, other_value):
        return term.BigInt(other_value.div(self.value))

    def arith_div_float(self, other_float):
        return term.Float(other_float / self.value.tofloat())

    # ------------------ power ------------------ 
    def arith_pow(self, other):
        return other.arith_pow_bigint(self.value)

    def arith_pow_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).pow(self.value))

    def arith_pow_bigint(self, other_value):
        return term.BigInt(other_value.pow(self.value))

    def arith_pow_float(self, other_float):
        return term.Float(other_float ** self.value.tofloat())

    # ------------------ shift right ------------------ 
    def arith_greaterthan_signgreaterthan_sign(self, other):
        return other.arith_shr_bigint(self.value)

    def arith_shr_number(self, other_num):
        try:
            num = rarithmetic.ovfcheck(int(self.value.str()))
        except OverflowError:
            raise ValueError('Right operand too big')
        return term.Number(other_num >> num)

    def arith_shr_bigint(self, other_value):
        try:
            num = rarithmetic.ovfcheck(int(self.value.str()))
        except OverflowError:
            raise ValueError('Right operand too big')
        return term.BigInt(other_value.rshift(num))

    # ------------------ shift left ------------------ 
    def arith_lessthan_signlessthan_sign(self, other):
        return other.arith_shl_bigint(self.value)

    def arith_shl_number(self, other_num):
        try:
            num = rarithmetic.ovfcheck(int(self.value.str()))
        except OverflowError:
            raise ValueError('Right operand too big')
        else:
            try:
                res = rarithmetic.ovfcheck(other_num << num)
            except OverflowError:
                return term.BigInt(rbigint.fromint(other_num).lshift(num))
            return term.Number(res)

    def arith_shl_bigint(self, other_value):
        try:
            num = rarithmetic.ovfcheck(int(self.value.str()))
        except OverflowError:
            raise ValueError('Right operand too big')
        return term.BigInt(other_value.lshift(num))

    # ------------------ or ------------------ 
    def arith_reverse_solidussolidus(self, other):
        return other.arith_or_bigint(self.value)

    def arith_or_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).or_(self.value))

    def arith_or_bigint(self, other_value):
        return term.BigInt(other_value.or_(self.value))

    # ------------------ and ------------------ 
    def arith_solidusreverse_solidus(self, other):
        return other.arith_and_bigint(self.value)

    def arith_and_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).and_(self.value))

    def arith_and_bigint(self, other_value):
        return term.BigInt(other_value.and_(self.value))

    # ------------------ xor ------------------ 
    def arith_xor(self, other):
        return other.arith_xor_bigint(self.value)

    def arith_xor_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).xor(self.value))

    def arith_xor_bigint(self, other_value):
        return term.BigInt(other_value.xor(self.value))

    # ------------------ mod ------------------ 
    def arith_mod(self, other):
        return other.arith_mod_bigint(self.value)

    def arith_mod_number(self, other_num):
        return term.BigInt(rbigint.fromint(other_num).mod(self.value))

    def arith_mod_bigint(self, other_value):
        return term.BigInt(other_value.mod(self.value))

    # ------------------ inversion ------------------ 
    def arith_reverse_solidus(self):
        return term.BigInt(self.value.invert())


    # ------------------ abs ------------------
    def arith_abs(self):
        return term.BigInt(self.value.abs())


    # ------------------ max ------------------
    def arith_max(self, other):
        return other.arith_max_bigint(self.value)

    def arith_max_number(self, other_num):
        other_value = rbigint.fromint(other_num)
        if other_value.lt(self.value):
            return term.BigInt(self.value)
        return term.BigInt(other_value)

    def arith_max_bigint(self, other_value):
        if other_value.lt(self.value):
            return term.BigInt(self.value)
        return term.BigInt(other_value)

    def arith_max_float(self, other_float):
        return term.Float(max(other_float, self.value.tofloat()))

    # ------------------ min ------------------
    def arith_min(self, other):
        return other.arith_min_bigint(self.value)

    def arith_min_number(self, other_num):
        other_value = rbigint.fromint(other_num)
        if other_value.lt(self.value):
            return term.BigInt(other_value)
        return term.BigInt(self.value)

    def arith_min_bigint(self, other_value):
        if other_value.lt(self.value):
            return term.BigInt(other_value)
        return term.BigInt(self.value)

    def arith_min_float(self, other_float):
        return term.Float(min(other_float, self.value.tofloat()))

    # ------------------ miscellanous ------------------
    def arith_round(self):
        return self

    def arith_floor(self):
        return self

    def arith_ceiling(self):
        return self

    def arith_arith_fractional_part(self):
        return term.Number(0)

    def arith_arith_integer_part(self):
        return self
