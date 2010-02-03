import prolog
import py
import time
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin


wall_start = time.time()
# TODO: make this continuation based and return all statistics
@expose_builtin("statistics", unwrap_spec=["atom", "obj"])
def impl_statistics(engine, heap, stat_name, value):
    if stat_name == 'runtime':        
        t = [clock_time(), clocktime_since_last_call()]
    if stat_name == 'walltime':
        t = [walltime(), walltime_since_last_call()]
    l = map(term.Number, t)
    helper.wrap_list(l).unify(value, heap)

clock_now = None
def clock_time():
    prolog.builtin.statistics.clock_now = int(time.clock()*1000)
    return prolog.builtin.statistics.clock_now
    
clock_last = 0
def clocktime_since_last_call():
    prolog.builtin.statistics.clock_last = prolog.builtin.statistics.clock_now - prolog.builtin.statistics.clock_last
    return prolog.builtin.statistics.clock_last
    
wall_now = 0
def walltime():
    prolog.builtin.statistics.wall_now = int(time.time()*1000)
    return prolog.builtin.statistics.wall_now    

wall_last = 0
def walltime_since_last_call():
    prolog.builtin.statistics.wall_last = prolog.builtin.statistics.wall_now - prolog.builtin.statistics.wall_last
    return prolog.builtin.statistics.wall_last
    
def reset_clocks():
    prolog.builtin.statistics.clock_last = prolog.builtin.statistics.clock_now = 0
    prolog.builtin.statistics.wall_last = prolog.builtin.statistics.wall_now = 0