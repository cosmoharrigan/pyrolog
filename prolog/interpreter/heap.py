from pypy.rlib import debug
from prolog.interpreter.term import BindingVar, AttVar

from pypy.rlib import jit

INIT_TRAIL_VAR = []
INIT_TRAIL_BINDING = []

class Heap(object):
    def __init__(self, prev=None):
        self.trail_var = INIT_TRAIL_VAR
        debug.make_sure_not_resized(self.trail_var)
        self.trail_binding = INIT_TRAIL_BINDING
        debug.make_sure_not_resized(self.trail_binding)
        self.i = 0
        self.trail_attrs = None
        self.prev = prev
        self.discarded = False
        self.hook = None

    # _____________________________________________________
    # interface that term.py uses
    def _find_not_discarded(self):
        while self is not None and self.discarded:
            self = self.prev
        return self

    def add_trail_atts(self, attvar, attr_name):
        if self._is_created_in_self(attvar):
            return
        value, index = attvar.get_attribute(attr_name)
        self._add_entry_trail_attrs(attvar, index, value)

    def trail_new_attr(self, attvar, index, value):
        if self._is_created_in_self(attvar):
            return
        self._add_entry_trail_attrs(attvar, index, value)

    def _add_entry_trail_attrs(self, attvar, index, value):
        entry = (attvar, index, value)
        if self.trail_attrs is None:
            self.trail_attrs = [entry]
        else:
            self.trail_attrs.append(entry)

    def add_trail(self, var):
        """ Remember the current state of a variable to be able to backtrack it
        to that state. Usually called just before a variable changes. """
        # if the variable doesn't exist before the last choice point, don't
        # trail it (variable shunting)
        if self._is_created_in_self(var):
            return
        i = self.i
        if i >= len(self.trail_var):
            self._double_size()
        self.trail_var[i] = var
        self.trail_binding[i] = var.binding
        self.i = i + 1

    def _is_created_in_self(self, var):
        created_in = var.created_after_choice_point
        if self is created_in: # fast path
            return True
        if created_in is not None and created_in.discarded:
            created_in = created_in._find_not_discarded()
            var.created_after_choice_point = created_in
        return self is created_in

    def _double_size(self):
        size = max(len(self.trail_var), 2)
        self.trail_var = self.trail_var + [None] * size
        self.trail_binding = self.trail_binding + [None] * size

    def newvar(self):
        """ Make a new variable. Should return a Var instance, possibly with
        interesting attributes set that e.g. add_trail can inspect."""
        result = BindingVar()
        result.created_after_choice_point = self
        return result

    def new_attvar(self):
        result = AttVar()
        result.created_after_choice_point = self
        return result

    def newvar_in_term(self, parent, index):
        from prolog.interpreter.term import var_in_term_classes
        result = var_in_term_classes[index](parent)
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
        for i in range(self.i-1, -1, -1):
            v = self.trail_var[i]
            assert v is not None
            v.binding = self.trail_binding[i]
            self.trail_var[i] = None
            self.trail_binding[i] = None
        self.i = 0

        if self.trail_attrs is not None:
            for attvar, index, value in self.trail_attrs:
                attvar.reset_field(index, value)

        self.trail_attrs = None
        self.hook = None

    def discard(self, current_heap):
        """ Remove a heap that is no longer needed (usually due to a cut) from
        a chain of frames. """
        self.discarded = True
        if current_heap.prev is self:
            if current_heap.i:
                self._discard_try_remove_current_trail(current_heap)
            if current_heap.trail_attrs is not None:
                self._discard_try_remove_current_trail_attvars(current_heap)

            # move the variable bindings from the discarded heap to the current
            # heap
            if self.i:
                self._discard_move_bindings_to_current(current_heap)

            if self.trail_attrs is not None:
                if current_heap.trail_attrs is not None:
                    current_heap.trail_attrs.extend(self.trail_attrs)
                else:
                    current_heap.trail_attrs = self.trail_attrs

            current_heap.prev = self.prev
            self.trail_var = None
            self.trail_binding = None
            self.trail_attrs = None
            self.i = -1
            self.prev = current_heap
        else:
            return self
        return current_heap


    def _discard_try_remove_current_trail(self, current_heap):
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

    def _discard_try_remove_current_trail_attvars(self, current_heap):
        trail_attrs = []
        targetpos = 0
        for var, attr, value in current_heap.trail_attrs:
            if var.created_after_choice_point is self:
                var.created_after_choice_point = self.prev
            else:
                trail_attrs[targetpos] = (var, attr, value)
        if not trail_attrs:
            trail_attrs = None
        current_heap.trail_attrs = trail_attrs


    def _discard_move_bindings_to_current(self, current_heap):
        for i in range(self.i):
            var = self.trail_var[i]
            currbinding = var.binding
            binding = self.trail_binding[i]

            var.binding = binding
            current_heap.add_trail(var)
            var.binding = currbinding

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

    # methods to for the hook chain

    def add_hook(self, attvar):
        self.hook = HookCell(attvar, self.hook)


class HookCell(object):
    def __init__(self, attvar, next=None):
        self.attvar = attvar
        self.next = next
