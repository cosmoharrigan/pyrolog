import py
import time
from prolog.interpreter.continuation import Engine
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true
from prolog.builtin.statistics import clock_time, reset_clocks, walltime

e = Engine()
def test_statistics():
    assert_true("statistics(runtime, X).", e)
    
def test_statistics_builds_list():
    assert_true('statistics(runtime, [A,B]), number(A), number(B).')
    
def test_statistics_runtime_total():
    reset_clocks()
    # first call returns total runtime in both list items
    clock = clock_time()
    vars = assert_true("statistics(runtime, [A,B]).")
    assert vars['A'].num == vars['B'].num
    assert clock <= vars['A'].num
    
def test_statistics_runtime_since_last_call():
    reset_clocks()
    # succesive call return total runtime and time since last call
    clock = clock_time()
    vars = assert_true("statistics(runtime, _), statistics(runtime, [A,B]).")
    assert vars['A'] != vars['B']
    assert clock <= vars['A'].num
    assert vars['B'].num <= clock
    
def test_statistics_walltime_total():
    reset_clocks()
    # first call returns total runtime in both list items
    clock = walltime()
    vars = assert_true("statistics(walltime, [A,B]).")
    assert vars['A'].num == vars['B'].num
    assert clock <= vars['A'].num

def test_statistics_walltime_since_last_call():
    reset_clocks()
    # succesive call return total runtime and time since last call
    clock = walltime()
    vars = assert_true("statistics(walltime, _), statistics(walltime, [A,B]).")
    assert vars['A'] != vars['B']
    assert clock <= vars['A'].num
    assert vars['B'].num <= clock
