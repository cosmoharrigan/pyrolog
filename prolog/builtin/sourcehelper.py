import os
import sys
from prolog.interpreter.error import throw_existence_error
from prolog.interpreter.term import Callable

path = os.path.dirname(__file__)
path = os.path.join(path, "..", "prolog_modules")

def get_source(filename):
    try:
        fd = os.open(filename, os.O_RDONLY, 0777)
    except OSError, e:
        try:
            fd = os.open(os.path.join(path, filename), os.O_RDONLY, 0777)
        except OSError, e:
            try:
                fd = os.open(filename + ".pl", os.O_RDONLY, 0777)
            except OSError, e:
                try:
                    fd = os.open(os.path.join(path, filename + ".pl"), os.O_RDONLY, 0777)
                except OSError, e:
                    throw_existence_error("source_sink", Callable.build(filename))
                    assert 0, "unreachable" # make the flow space happy
    try:
        content = []
        while 1:
            s = os.read(fd, 4096)
            if not s:
                break
            content.append(s)
        file_content = "".join(content)
    finally:
        os.close(fd)
    return file_content
