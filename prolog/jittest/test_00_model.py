from __future__ import with_statement
import sys, os
import types
import subprocess
import py
from lib_pypy import disassembler
from pypy.tool.udir import udir
from pypy.tool import logparser
from pypy.jit.tool.jitoutput import parse_prof
from prolog.jittest.model import Log, \
    OpMatcher

executable = py.path.local(__file__).dirpath().dirpath().join("pyrolog-c")
assert executable.check()
strexecutable = str(executable)

class BaseTestPyrologC(object):
    def setup_class(cls):
        if not executable.check():
            py.test.skip("missing pyrolog-c at %s" % (executable.dirpath(), ))
        cls.tmpdir = udir.join('test-pyrolog-jit')
        cls.tmpdir.ensure(dir=True)

    def setup_method(self, meth):
        self.filepath = self.tmpdir.join(meth.im_func.func_name + '.pl')

    def run(self, src, call, **jitopts):
        jitopts.setdefault('threshold', 200)
        # write the snippet
        with self.filepath.open("w") as f:
            # we don't want to see the small bridges created
            # by the checkinterval reaching the limit
            f.write(str(src) + "\n")
        #
        # run a child pyrolog-c with logging enabled
        logfile = self.filepath.new(ext='.log')
        #
        cmdline = [strexecutable]
        cmdline.append(str(self.filepath))
        #
        print cmdline, logfile
        env={'PYPYLOG': 'jit-log-opt,jit-summary:' + str(logfile)}
        #env={'PYPYLOG': ':' + str(logfile)}
        pipe = subprocess.Popen(cmdline,
                                env=env,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        pipe.stdin.write(call + "\n")
        stdout, stderr = pipe.communicate()
        if stderr.startswith('SKIP:'):
            py.test.skip(stderr)
        if stderr.startswith('debug_alloc.h:'):   # lldebug builds
            stderr = ''
        assert not stderr
        #
        # parse the JIT log
        rawlog = logparser.parse_log_file(str(logfile))
        rawtraces = logparser.extract_category(rawlog, 'jit-log-opt-')
        log = Log(rawtraces)
        log.result = stdout
        if "ParseError" in log.result or "ERROR" in log.result:
            assert 0, log.result
        #
        summaries  = logparser.extract_category(rawlog, 'jit-summary')
        if len(summaries) > 0:
            log.jit_summary = parse_prof(summaries[-1])
        else:
            log.jit_summary = None
        #
        return log

    def run_and_check(self, src, args=[], **jitopts):
        log1 = self.run(src, args, threshold=-1, function_threshold=-1)  # without the JIT
        log2 = self.run(src, args, **jitopts)     # with the JIT
        assert log1.result == log2.result
        # check that the JIT actually ran
        assert len(log2.filter_loops()) > 0
        return log2


class TestOpMatcher(object):

    def match(self, src1, src2, **kwds):
        from pypy.tool.jitlogparser.parser import SimpleParser
        loop = SimpleParser.parse_from_input(src1)
        matcher = OpMatcher(loop.operations, src=src1)
        return matcher.match(src2, **kwds)

    def test_match_var(self):
        match_var = OpMatcher([]).match_var
        assert match_var('v0', 'V0')
        assert not match_var('v0', 'V1')
        assert match_var('v0', 'V0')
        #
        # for ConstPtr, we allow the same alpha-renaming as for variables
        assert match_var('ConstPtr(ptr0)', 'PTR0')
        assert not match_var('ConstPtr(ptr0)', 'PTR1')
        assert match_var('ConstPtr(ptr0)', 'PTR0')
        #
        # for ConstClass, we want the exact matching
        assert match_var('ConstClass(foo)', 'ConstClass(foo)')
        assert not match_var('ConstClass(bar)', 'v1')
        assert not match_var('v2', 'ConstClass(baz)')
        #
        # the var '_' matches everything (but only on the right, of course)
        assert match_var('v0', '_')
        assert match_var('v0', 'V0')
        assert match_var('ConstPtr(ptr0)', '_')
        py.test.raises(AssertionError, "match_var('_', 'v0')")

    def test_parse_op(self):
        res = OpMatcher.parse_op("  a =   int_add(  b,  3 ) # foo")
        assert res == ("int_add", "a", ["b", "3"], None)
        res = OpMatcher.parse_op("guard_true(a)")
        assert res == ("guard_true", None, ["a"], None)
        res = OpMatcher.parse_op("setfield_gc(p0, i0, descr=<foobar>)")
        assert res == ("setfield_gc", None, ["p0", "i0"], "<foobar>")
        res = OpMatcher.parse_op("i1 = getfield_gc(p0, descr=<foobar>)")
        assert res == ("getfield_gc", "i1", ["p0"], "<foobar>")
        res = OpMatcher.parse_op("p0 = force_token()")
        assert res == ("force_token", "p0", [], None)

    def test_exact_match(self):
        loop = """
            [i0]
            i2 = int_add(i0, 1)
            jump(i2)
        """
        expected = """
            i5 = int_add(i2, 1)
            jump(i5, descr=...)
        """
        assert self.match(loop, expected)
        #
        expected = """
            i5 = int_sub(i2, 1)
            jump(i5, descr=...)
        """
        assert not self.match(loop, expected)
        #
        expected = """
            i5 = int_add(i2, 1)
            jump(i5, descr=...)
            extra_stuff(i5)
        """
        assert not self.match(loop, expected)
        #
        expected = """
            i5 = int_add(i2, 1)
            # missing op at the end
        """
        assert not self.match(loop, expected)

    def test_match_descr(self):
        loop = """
            [p0]
            setfield_gc(p0, 1, descr=<foobar>)
        """
        assert self.match(loop, "setfield_gc(p0, 1, descr=<foobar>)")
        assert self.match(loop, "setfield_gc(p0, 1, descr=...)")
        assert self.match(loop, "setfield_gc(p0, 1, descr=<.*bar>)")
        assert not self.match(loop, "setfield_gc(p0, 1)")
        assert not self.match(loop, "setfield_gc(p0, 1, descr=<zzz>)")


    def test_partial_match(self):
        loop = """
            [i0]
            i1 = int_add(i0, 1)
            i2 = int_sub(i1, 10)
            i3 = int_floordiv(i2, 100)
            i4 = int_mul(i1, 1000)
            jump(i4)
        """
        expected = """
            i1 = int_add(0, 1)
            ...
            i4 = int_mul(i1, 1000)
            jump(i4, descr=...)
        """
        assert self.match(loop, expected)

    def test_partial_match_is_non_greedy(self):
        loop = """
            [i0]
            i1 = int_add(i0, 1)
            i2 = int_sub(i1, 10)
            i3 = int_mul(i2, 1000)
            i4 = int_mul(i1, 1000)
            jump(i4, descr=...)
        """
        expected = """
            i1 = int_add(0, 1)
            ...
            _ = int_mul(_, 1000)
            jump(i4, descr=...)
        """
        # this does not match, because the ... stops at the first int_mul, and
        # then the second one does not match
        assert not self.match(loop, expected)

    def test_partial_match_at_the_end(self):
        loop = """
            [i0]
            i1 = int_add(i0, 1)
            i2 = int_sub(i1, 10)
            i3 = int_floordiv(i2, 100)
            i4 = int_mul(i1, 1000)
            jump(i4)
        """
        expected = """
            i1 = int_add(0, 1)
            ...
        """
        assert self.match(loop, expected)

    def test_ignore_opcodes(self):
        loop = """
            [i0]
            i1 = int_add(i0, 1)
            i4 = force_token()
            i2 = int_sub(i1, 10)
            jump(i4)
        """
        expected = """
            i1 = int_add(i0, 1)
            i2 = int_sub(i1, 10)
            jump(i4, descr=...)
        """
        assert self.match(loop, expected, ignore_ops=['force_token'])

    def test_match_dots_in_arguments(self):
        loop = """
            [i0]
            i1 = int_add(0, 1)
            jump(i4, descr=...)
        """
        expected = """
            i1 = int_add(...)
            jump(i4, descr=...)
        """
        assert self.match(loop, expected)


class TestRunPyrologC(BaseTestPyrologC):

    def test_run_function(self):
        code = """
        length(L, O) :- length(L, 0, O).
        length([], O, O).
        length([_ | T], I, O) :- I1 is I + 1, length(T, I1, O).
        """
        log = self.run(code, "append([1, 2, 3], [3, 4, 5], X), length(X, Y).")
        assert "Y = 6" in log.result

    def test_check_logs(self):
        code = """
        loop(0).
        loop(X) :- X > 0, X0 is X - 1, loop(X0).
        """
        log = self.run_and_check(code, "loop(100000000).")
        loop, = log.filter_loops()
        loop.match("""
            i5 = int_gt(i1, 0)
            guard_true(i5, descr=<Guard2>)
            i7 = int_sub(i1, 1)
            guard_not_invalidated(descr=<Guard3>)
            i10 = int_eq(i7, 0)
            guard_false(i10, descr=<Guard4>)
            jump(p0, i7, p2, p3, descr=<Loop0>)
        """)


    def test_append(self):
        code = """
        loop(0, []).
        loop(X, [a | T]) :- X > 0, X0 is X - 1, loop(X0, T).
        length([], O, O).
        length([_|T], I, O) :- I1 is I + 1, length(T, I1, X0).
        """
        log = self.run_and_check(code, "loop(10000, A), loop(1000, B), append(A, B, C), length(C, 0, D).")
        # assert "D = 11000" in log.result # XXX fix this!
        loop, = log.filter_loops("append")
        assert loop.match("""
            guard_nonnull(p6, descr=...)
            i9 = ptr_eq(p6, ConstPtr(ptr8))
            guard_false(i9, descr=...)
            p10 = getfield_gc(p3, descr=...)
            guard_nonnull(p10, descr=...)
            i11 = getfield_gc(p10, descr=...) # inst_discarded
            guard_false(i11, descr=...)
            i12 = ptr_eq(p5, p10)
            guard_true(i12, descr=...)
            guard_nonnull_class(p7, 136989568, descr=...)
            i16 = ptr_eq(p7, ConstPtr(ptr15))
            guard_false(i16, descr=...)
            guard_not_invalidated(descr=...)
            p18 = new_with_vtable(136988224)
            setfield_gc(p18, p6, descr=...)  # inst_val_0
            p20 = new_with_vtable(136989568)
            setfield_gc(p20, p5, descr=...)  # inst_created_after_choice_point
            setfield_gc(p18, p20, descr=...) # inst_val_1
            setfield_gc(p3, p18, descr=...)  # inst_binding
            p21 = getfield_gc(p7, descr=...) # inst_binding
            guard_nonnull_class(p21, 136988224, descr=...)
            p23 = getfield_gc_pure(p21, descr=...)  # inst_val_0
            p24 = getfield_gc_pure(p21, descr=...) # inst_val_1
            p25 = getfield_gc(p20, descr=...) # inst_binding
            guard_isnull(p25, descr=...)
            jump(p0, p7, p2, p20, p4, p5, p23, p24, descr=...)
        """)
        loop, = log.filter_loops("length")
        assert loop.match("""
            guard_nonnull_class(p5, 136989568, descr=...)
            i8 = ptr_eq(p5, ConstPtr(ptr7))
            guard_false(i8, descr=...)
            i10 = int_add_ovf(i2, 1)
            guard_no_overflow(descr=...)
            guard_not_invalidated(descr=...)
            p12 = getfield_gc(p5, descr=...) # inst_binding
            guard_nonnull_class(p12, 136988224, descr=...)
            p14 = getfield_gc_pure(p12, descr=...) # inst_val_0
            p15 = getfield_gc_pure(p12, descr=...) # inst_val_1
            jump(p0, p5, i10, p3, p4, p15, descr=...)

        """)
