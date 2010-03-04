import py
import time
from prolog.interpreter.continuation import Engine
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true
from prolog.builtin.statistics import clock_time, reset_clocks, walltime

e = Engine()
def test_statistics():
    assert_true("statistics(runtime, X).", e)
    
def test_statistics_builds_list():
    assert_true('statistics(runtime, [A,B]), number(A), number(B).', e)
    
def test_statistics_runtime_total():
    reset_clocks(e)
    # first call returns total runtime in both list items
    clock = clock_time(e)
    vars = assert_true("statistics(runtime, [A,B]).", e)
    assert vars['A'].num == vars['B'].num
    assert vars['A'] != 0
    assert clock <= vars['A'].num
    
def test_statistics_runtime_since_last_call():
    reset_clocks(e)
    # succesive call return total runtime and time since last call
    clock = clock_time(e)
    vars = assert_true("statistics(runtime, _), statistics(runtime, [A,B]).", e)
    assert vars['A'] != vars['B']
    assert clock <= vars['A'].num
    assert vars['B'].num <= clock
    
def test_statistics_walltime_total():
    reset_clocks(e)
    # first call returns total runtime in both list items
    clock = walltime(e)
    vars = assert_true("statistics(walltime, [A,B]).", e)
    assert vars['A'].num == vars['B'].num
    assert vars['A'].num != 0
    assert clock <= vars['A'].num

def test_statistics_walltime_since_last_call():
    # succesive call return total runtime and time since last call
    clock = walltime(e)
    reset_clocks(e)
    vars = assert_true("statistics(walltime, _), statistics(walltime, [A,B]).", e)
    assert vars['A'] != vars['B']
    assert clock <= vars['A'].num
    assert vars['B'].num <= clock


def test_statistics_walltime_progresses():
    # succesive call return total runtime and time since last call
    clock = walltime(e)
    reset_clocks(e)
    vars = assert_true("statistics(walltime, _), statistics(walltime, [A,B]).", e)
    time.sleep(2)
    vars = assert_true("statistics(walltime, _), statistics(walltime, [C,D]).", e)
    assert vars['A'] != vars['B']
    assert clock <= vars['A'].num
    assert vars['B'].num <= clock
