import os
import py
from prolog.interpreter.error import throw_existence_error

def get_source(filename):
    #import pdb; pdb.set_trace()
    path = str(py.path.local(__file__).dirpath().join("../prolog_modules")) + "/"
    try:
        fd = os.open(filename, os.O_RDONLY, 0777)
    except OSError, e:
        try:
            fd = os.open(path + filename, os.O_RDONLY, 0777)
        except OSError, e:
            pl = filename.endswith(".pl")
            try:
                if pl:
                    fd = os.open(filename[:len(filename) - 3], os.O_RDONLY, 0777)
                else:
                    fd = os.open(filename + ".pl", os.O_RDONLY, 0777)
            except OSError, e:
                try:
                    if pl:
                        fd = os.open(path + filename[:len(filename) - 3], os.O_RDONLY, 0777)
                    else:
                        fd = os.open(path + filename + ".pl", os.O_RDONLY, 0777)
                except OSError, e:
                    throw_existence_error("source_sink", filename)
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
