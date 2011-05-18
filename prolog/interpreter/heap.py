from prolog.interpreter.term import Var, AttVar

from pypy.rlib import jit

class Heap(object):
    INITSIZE = 2
    def __init__(self, prev=None):
        self.trail_var = [None] * Heap.INITSIZE
        self.trail_binding = [None] * Heap.INITSIZE
        self.i = 0
        self.trail_attrs = []
        self.hooks = HookChain()
        self.prev = prev
        self.discarded = False

    # _____________________________________________________
    # interface that term.py uses

    def add_trail_atts(self, attvar, attr_name):
        if self._is_created_in_self(attvar):
            return
        self.trail_attrs.append((attvar, attr_name, attvar.atts.get(attr_name, None)))

    def add_trail(self, var):
        """ Remember the current state of a variable to be able to backtrack it
        to that state. Usually called just before a variable changes. """
        # if the variable doesn't exist before the last choice point, don't
        # trail it (variable shunting)
        if self._is_created_in_self(var):
            return
        #i = jit.hint(self.i, promote=True)
        i = self.i
        if i >= len(self.trail_var):
            self._double_size()
        self.trail_var[i] = var
        self.trail_binding[i] = var.binding
        self.i = i + 1

    def add_hook(self, attvar):
        self.hooks.add_hook(attvar)

    def _find_not_discarded(self):
        while self is not None and self.discarded:
            self = self.prev
        return self

    def _is_created_in_self(self, var):
        created_in = var.created_after_choice_point
        if created_in is not None and created_in.discarded:
            created_in = created_in._find_not_discarded()
            var.created_after_choice_point = created_in
        return self is created_in

    def _double_size(self):
        trail_var = [None] * (len(self.trail_var) * 2)
        l = len(trail_var)
        trail_binding = [None] * l
        for i in range(self.i):
            trail_var[i] = self.trail_var[i]
            trail_binding[i] = self.trail_binding[i]
        self.trail_var = trail_var
        self.trail_binding = trail_binding

    def newvar(self):
        """ Make a new variable. Should return a Var instance, possibly with
        interesting attributes set that e.g. add_trail can inspect."""
        result = Var()
        result.created_after_choice_point = self
        return result

    def new_attvar(self):
        result = AttVar()
        result.created_after_choice_point = self
        return result

    # _____________________________________________________

    def branch(self):
        """ Branch of a heap for a choice point. The return value is the new
        heap that should be used from now on, self is the heap that can be
        backtracked to."""
        res = Heap(self)
        return res

    @jit.unroll_safe
    def revert_upto(self, heap, discard_choicepoint=False):
        """ Revert to the heap corresponding to a choice point. The return
        value is the new heap that should be used."""
        previous = self
        while self is not heap:
            if self is None:
                break
            self._revert()
            previous = self
            self = self.prev
        if discard_choicepoint:
            return heap
        return previous

    @jit.unroll_safe
    def _revert(self):
        assert not self.discarded
        for i in range(self.i-1, -1, -1):
            v = self.trail_var[i]
            assert v is not None
            v.binding = self.trail_binding[i]
            self.trail_var[i] = None
            self.trail_binding[i] = None
        self.i = 0

        for attvar, name, value in self.trail_attrs:
            if value is None:
                del attvar.atts[name]
            else:
                attvar.atts[name] = value
        self.trail_attrs = []
        self.hooks.clear()

    @jit.unroll_safe
    def discard(self, current_heap):
        """ Remove a heap that is no longer needed (usually due to a cut) from
        a chain of frames. """
        self.discarded = True
        if current_heap.prev is self:
            targetpos = 0
            # check whether variables in the current heap no longer need to be
            # traced, because they originate in the discarded heap
            for i in range(current_heap.i):
                var = current_heap.trail_var[i]
                binding = current_heap.trail_binding[i]
                if var.created_after_choice_point is self:
                    var.created_after_choice_point = self.prev
                    current_heap.trail_var[i] = None
                    current_heap.trail_binding[i] = None
                else:
                    current_heap.trail_var[targetpos] = var
                    current_heap.trail_binding[targetpos] = binding
                    targetpos += 1
            current_heap.i = targetpos

            trail_attrs = []
            targetpos = 0
            for var, attr, value in current_heap.trail_attrs:
                if var.created_after_choice_point is self:
                    var.created_after_choice_point = self.prev
                else:
                    trail_attrs[targetpos] = (var, attr, value)
            current_heap.trail_attrs = trail_attrs

            # move the variable bindings from the discarded heap to the current
            # heap
            for i in range(self.i):
                var = self.trail_var[i]
                currbinding = var.binding
                binding = self.trail_binding[i]

                var.binding = binding
                current_heap.add_trail(var)
                var.binding = currbinding

            for attvar, name, value in self.trail_attrs:
                current_val = attvar.atts[name]
                attvar.atts[name] = value
                current_heap.add_trail_atts(attvar, name)
                attvar.atts[name] = current_val

            current_heap.prev = self.prev
            self.trail_var = None
            self.trail_binding = None
            self.i = -1
            # make self.prev point to the heap that replaced it
            self.prev = current_heap
        else:
            return self
        return current_heap


    def __repr__(self):
        return "<Heap %r trailed vars>" % (self.i, )

    def _dot(self, seen):
        if self in seen:
            return
        seen.add(self)
        yield '%s [label="%r", shape=octagon]' % (id(self), self)
        if self.prev:
            yield "%s -> %s [label=prev]" % (id(self), id(self.prev))
            for line in self.prev._dot(seen):
                yield line

class HookChain(object):
    def __init__(self):
        self.last = None

    def add_hook(self, hook):
        cell = HookCell(hook)
        if self.last is None:
            self.last = cell
        else:
            cell.next = self.last
            self.last = cell

    def clear(self):
        self.__init__()

    def _size(self):
        if self.last is None:
            return 0
        current = self.last
        size = 0
        while current is not None:
            current = current.next
            size += 1
        return size

class HookCell(object):
    def __init__(self, hook):
        self.hook = hook
        self.next = None
