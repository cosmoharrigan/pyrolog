import os
from prolog.interpreter.error import throw_existence_error

def get_source(filename):
    try:
        fd = os.open(filename, os.O_RDONLY, 0777)
    except OSError, e:
        try:
            if filename.endswith(".pl"):
                fd = os.open(filename[:len(filename) - 3], os.O_RDONLY, 0777)
            else:
                fd = os.open(filename + ".pl", os.O_RDONLY, 0777)
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
