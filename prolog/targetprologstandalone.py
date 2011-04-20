"""
A simple standalone target for the prolog interpreter.
"""

import sys
from prolog.interpreter.translatedmain import repl, execute

# __________  Entry point  __________

from prolog.interpreter.continuation import Engine
from prolog.interpreter import term
from prolog.interpreter import arithmetic # for side effects
from prolog import builtin # for side effects
e = Engine(load_system=False)
term.DEBUG = False

def entry_point(argv):
    e.clocks.startup()
    if len(argv) == 2:
        execute(e, argv[1])
    try:
        repl(e)
    except SystemExit:
        return 1
    return 0

# _____ Define and setup target ___


def target(driver, args):
    driver.exe_name = 'pyrolog-%(backend)s'
    return entry_point, None

def portal(driver):
    from prolog.interpreter.portal import get_portal
    return get_portal(driver)

def jitpolicy(self):
    from pypy.jit.codewriter.policy import JitPolicy
    return JitPolicy()

if __name__ == '__main__':
    entry_point(sys.argv)
