import os, py

#TESTDIR = py.path.local(__file__).dirpath().join('inriasuite') # use this line instead of the next
TESTDIR = 'inriasuite'

def deconstruct_line(line):

    HALT = 'halt,'
    FAIL = 'fail,'
    TRUE = 'true,'
    FLOAT = '0.33'
    ASSIGN = 'X ='
    CUT = '!,'
    line_0_5 = line[0:5]
    H_F_T = (HALT, FAIL, TRUE)
    
    # use str.startswith instead of [...]
    if line_0_5 in H_F_T:
        if line_0_5 == FAIL:
            left = 'fail'
        elif line_0_5 == HALT:
            left = 'halt'
        elif line_0_5 == TRUE:
            left = 'true'
        right = line[6:]
    elif line[0:2] == CUT:
        left = '!'
        right = line[3:]
    elif line[0:3] == ASSIGN:
        left = 'X = "fred"'
        right = line[12:]
    elif line[0:4] == FLOAT:
        left = '0.333 =:= 1/3'
        right = line[15:]
    else:
        first_open_par = line.find('(')
        brace_counter = 1
        i = first_open_par
        while brace_counter:
            i += 1
            if line[i] == '(':
                brace_counter += 1
            elif line[i] == ')':
                brace_counter -= 1
        left = line[0:i + 1]
        right = line[i + 2:].strip()
    return left, right
    

def get_lines(file_):
    testfile = open(TESTDIR + '/' + file_)
    for test in testfile.readlines():
        if test.endswith('%%SKIP%%\n'):
            continue
        if test.startswith('['):
            last_bracket = test.rfind(']')
            first_bracket = test.find('[') + 1
            relevant = test[first_bracket:last_bracket]
            left, right = deconstruct_line(relevant)
            yield left, right


def deconstruct_list(l):
    pieces = [piece for piece in l.split('], [')]
    pieces[0] = pieces[0][1:]
    return pieces


def get_files():
    _, _, content = os.walk(TESTDIR).next()
    for file_ in content:
        yield file_


def main():
    errors = 0
    lists = 0
    results = 0
    count = 0
    other = 0

    for f in get_files():
        for left, right in get_lines(f):
            if right.find('error') != -1:
                errors += 1
            elif right.find('[') != -1:
                pieces = deconstruct_list(right[1:-2])
                lists += 1
            elif right in ('failure', 'success'):
                results += 1
            else:
                other += 1
            count += 1

    print '==============================='
    print '%10s: %3d' % ('TOTAL', count)
    print '%10s: %3d' % ('RESULTS', results)
    print '%10s: %3d' % ('ERRORS', errors)
    print '%10s: %3d' % ('LISTS', lists)
    print '%10s: %3d' % ('OTHER', other)
    print '%10s: %3d' % ('SUM', results + errors + lists + other)
    print '=============================='


if __name__ == '__main__':
    main()
