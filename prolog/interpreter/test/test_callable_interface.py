from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.term import Atom, Number, Term, Callable
import py

def parse(inp):
    t = parse_file(inp)
    builder = TermBuilder()
    return builder.build(t)
    
atom = parse('a.')[0]
term = parse('t(a, b, c, d, f).')[0]
def test_atom_get_signature():
    r = atom.get_prolog_signature() 
    r.name() == '/'
    r._args[0] == Callable.build('a')
    r._args[1] == Number(0)

def test_atom_get_arguments():
    assert atom.arguments() == []
    
def test_atom_arguemtn_count():
    assert atom.argument_count() == 0
    
def test_atom_get_argument_at():
    assert py.test.raises(IndexError, 'atom.argument_at(0)')
    
def test_term_get_signature():
    r = term.get_prolog_signature()
    print r
    assert r.name() == '/'
    assert r._args[0].name() == 't'
    assert r._args[1].num == 5
    
def test_term_get_arguments():
    t = term.arguments()
    assert isinstance(t, list)
    assert len(t) == 5
    
def test_term_get_argument_out_of_range():
    py.test.raises(IndexError, 'term.argument_at(5)')

def test_term_get_argument_in_range():
    t =  term.argument_at(2)
    assert t.name() == 'c'
    
def test_term_argument_count():
    assert term.argument_count() == 5
    
def test_callable_name():
    c = Callable()
    py.test.raises(NotImplementedError, 'c.name()')
    
def test_callable_signature():
    c = Callable()
    py.test.raises(NotImplementedError, 'c.signature()')
    
def test_atom_name():
    assert atom.name() == 'a'

def test_atom_signature():
    assert atom.signature() == 'a/0'
    
def test_term_name():
    assert term.name() == 't'
    
def test_term_signature():
    assert term.signature() == 't/5'
    
def test_callable_factory_for_atom():
    r = Callable.build('foo')
    assert isinstance(r, Atom)
    assert r.signature() == 'foo/0'

def test_callable_factory_for_term_with_empty_args():
    r = Callable.build('bar', [])
    assert isinstance(r, Atom)
    assert r.signature() == 'bar/0'

def test_callable_factory_for_term():
    r = Callable.build('foo', [1, 2])
    assert isinstance(r, Term)
    assert r.signature() == 'foo/2'