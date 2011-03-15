from prolog.interpreter.term import Var, AttVar

from pypy.rlib import jit

class Heap(object):
    INITSIZE = 2
    def __init__(self, prev=None):
        self.trail_var = [None] * Heap.INITSIZE
        self.trail_binding = [None] * Heap.INITSIZE
        self.trail_atts = [None] * Heap.INITSIZE
        self.i = 0
        self.prev = prev
        self.discarded = False

    # _____________________________________________________
    # interface that term.py uses

    def add_trail(self, var):
        """ Remember the current state of a variable to be able to backtrack it
        to that state. Usually called just before a variable changes. """
        # if the variable doesn't exist before the last choice point, don't
        # trail it (variable shunting)
        created_in = var.created_after_choice_point
        if created_in is not None and created_in.discarded:
            created_in = created_in._find_not_discarded()
            var.created_after_choice_point = created_in
        if self is created_in:
            return
        # actually trail the variable
        i = jit.hint(self.i, promote=True)
        if i >= len(self.trail_var):
            self._double_size()
        self.trail_var[i] = var
        self.trail_binding[i] = var.binding
        self.i = i + 1

    def add_trail_atts(self, attvar):
        assert isinstance(attvar, AttVar) 
        created_in = attvar.created_after_choice_point
        if created_in is not None and created_in.discarded:
            created_in = created_in._find_not_discarded()
            attvar.created_after_choice_point = created_in
        if self is created_in:
            return
        # actually trail the variable
        i = jit.hint(self.i, promote=True)
        if i >= len(self.trail_var):
            self._double_size()
        self.trail_var[i] = attvar
        self.trail_binding[i] = attvar.binding
        self.trail_atts[i] = attvar.atts.copy()
        self.i = i + 1


    def _find_not_discarded(self):
        while self is not None and self.discarded:
            self = self.prev
        return self

    @jit.unroll_safe
    def _double_size(self):
        trail_var = [None] * (len(self.trail_var) * 2)
        l = len(trail_var)
        trail_binding = [None] * l
        trail_atts = [None] * l
        for i in range(self.i):
            trail_var[i] = self.trail_var[i]
            trail_binding[i] = self.trail_binding[i]
            trail_atts[i] = self.trail_atts[i]
        self.trail_var = trail_var
        self.trail_binding = trail_binding
        self.trail_atts = trail_atts

    def newvar(self):
        """ Make a new variable. Should return a Var instance, possibly with
        interesting attributes set that e.g. add_trail can inspect."""
        result = Var()
        result.created_after_choice_point = self
        return result

    def new_attvar(self):
        result = AttVar(None)
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
            self.trail_var[i].binding = self.trail_binding[i]
            if isinstance(v, AttVar) and self.trail_atts[i]:
                v.atts.clear()
                for key, val in self.trail_atts[i].iteritems():
                    v.atts[key] = val
                self.trail_atts[i] = None
            self.trail_var[i] = None
            self.trail_binding[i] = None
        self.i = 0

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
                atts = current_heap.trail_atts[i]
                if var.created_after_choice_point is self:
                    var.created_after_choice_point = self.prev
                    current_heap.trail_var[i] = None
                    current_heap.trail_binding[i] = None
                    current_heap.trail_atts[i] = None
                else:
                    current_heap.trail_var[targetpos] = var
                    current_heap.trail_binding[targetpos] = binding
                    current_heap.trail_atts[targetpos] = atts
                    targetpos += 1
            current_heap.i = targetpos

            # move the variable bindings from the discarded heap to the current
            # heap
            for i in range(self.i):
                var = self.trail_var[i]
                currbinding = var.binding
                binding = self.trail_binding[i]

                var.binding = binding
                if isinstance(var, AttVar):
                    current_atts = var.atts
                    atts = self.trail_atts[i]
                    if atts:
                        var.atts = atts.copy()
                    current_heap.add_trail_atts(var)
                    var.atts = current_atts
                else:
                    current_heap.add_trail(var)
                var.binding = currbinding

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
