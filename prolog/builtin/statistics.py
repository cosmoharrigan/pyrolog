import prolog
import py
import time
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin


wall_start = time.time()
# TODO: make this continuation based and return all statistics
# RPYTHON??
@expose_builtin("statistics", unwrap_spec=["atom", "obj"])
def impl_statistics(engine, heap, stat_name, value):
    t = []
    if stat_name == 'runtime':        
        t = [clock_time(), clocktime_since_last_call()]
    if stat_name == 'walltime':
        t = [walltime(), walltime_since_last_call()]
    l = [term.Number(x) for x in t]
    helper.wrap_list(l).unify(value, heap)
    
start = int(time.time())
clocks = {'cpu_last': 0, 'cpu_now': 0, 'wall_now':0, 'wall_last':0}

def clock_time():
    clocks['cpu_now'] = int(time.clock()*1000)
    return clocks['cpu_now']
    
def clocktime_since_last_call():
    t = clocks['cpu_now'] - clocks['cpu_last']
    clocks['cpu_last'] = clocks['cpu_now']
    return t
    
def walltime():
    clocks['wall_now'] = int((time.time()-start)*1000)
    return clocks['wall_now']

def walltime_since_last_call():
    t = clocks['wall_now'] - clocks['wall_last']
    clocks['wall_last'] = clocks['wall_now']
    return t
    
def reset_clocks():
    prolog.builtin.statistics.clocks = {'cpu_last': 0, 'cpu_now': 0, 'wall_now':0, 'wall_last':0}