import prolog
import py
import time
from prolog.interpreter import helper, term, error
from prolog.builtin.register import expose_builtin


# TODO: make this continuation based and return all statistics
# RPYTHON??
@expose_builtin("statistics", unwrap_spec=["atom", "obj"])
def impl_statistics(engine, heap, stat_name, value):
    t = []
    if stat_name == 'runtime':
        t = [clock_time(engine), clocktime_since_last_call(engine)]
    if stat_name == 'walltime':
        t = [walltime(engine), walltime_since_last_call(engine)]
    l = [term.Number(x) for x in t]
    helper.wrap_list(l).unify(value, heap)

def clock_time(engine):
    engine.clocks['cpu_now'] = int(time.clock()*1000)
    return engine.clocks['cpu_now']

def clocktime_since_last_call(engine):
    t = engine.clocks['cpu_now'] - engine.clocks['cpu_last']
    engine.clocks['cpu_last'] = engine.clocks['cpu_now']
    return t

def walltime(engine):
    # XXX Unhack
    engine.clocks['wall_now'] = millis()
    return engine.clocks['wall_now']

def walltime_since_last_call(engine):
    t = engine.clocks['wall_now'] - engine.clocks['wall_last']
    engine.clocks['wall_last'] = engine.clocks['wall_now']
    return t

def reset_clocks(engine):
    engine.clocks = {'cpu_last': 0, 'cpu_now': 0, 'wall_now':0, 'wall_last':0}

def millis():
    x = time.time()
    y = int(x)
    dec = int((x - y)*100)
    h = y % 100
    return (h*100+dec)