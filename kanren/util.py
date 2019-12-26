from itertools import chain, islice
from collections.abc import Hashable, MutableSet, Set


class FlexibleSet(MutableSet):
    """A set that uses a list (and costly identity check) for unhashable items."""

    __slots__ = ("set", "list")

    def __init__(self, iterable):

        self.set = set()
        self.list = []

        for i in iterable:
            self.add(i)

    def add(self, item):
        try:
            self.set.add(item)
        except TypeError:
            # TODO: Could try `multihash`.
            # TODO: Use `bisect` for unhashable but orderable elements
            if item not in self.list:
                self.list.append(item)

    def discard(self, item):
        try:
            self.remove(item)
        except KeyError:
            pass

    def clear(self):
        self.set.clear()
        self.list.clear()

    def pop(self):
        try:
            return self.set.pop()
        except (TypeError, KeyError):
            try:
                return self.list.pop(-1)
            except IndexError:
                raise KeyError()

    def remove(self, item):
        try:
            self.set.remove(item)
        except (TypeError, KeyError):
            try:
                self.list.remove(item)
            except ValueError:
                raise KeyError()

    def __le__(self, other):
        raise NotImplementedError()

    def __ge__(self, other):
        raise NotImplementedError()

    def __ior__(self, item):
        raise NotImplementedError()

    def __iand__(self, item):
        raise NotImplementedError()

    def __ixor__(self, item):
        raise NotImplementedError()

    def __isub__(self, item):
        raise NotImplementedError()

    def __iter__(self):
        return chain(self.set, self.list)

    def __contains__(self, value):
        try:
            return value in self.set or value in self.list
        except TypeError:
            return value in self.list

    def __len__(self):
        return len(self.set) + len(self.list)

    def __eq__(self, other):
        if type(self) == type(other):
            return self.set == other.set and self.list == other.list
        elif isinstance(other, Set):
            return len(self.list) == 0 and other.issuperset(self.set)

        return NotImplemented

    def __repr__(self):
        return f"FlexibleSet([{', '.join(str(s) for s in self)}])"


def hashable(x):
    try:
        hash(x)
        return True
    except TypeError:
        return False


def dicthash(d):
    return hash(frozenset(d.items()))


def multihash(x):
    try:
        return hash(x)
    except TypeError:
        if isinstance(x, (list, tuple, set, frozenset)):
            return hash(tuple(multihash(i) for i in x))
        if type(x) is dict:
            return hash(frozenset(tuple(multihash(i) for i in x.items())))
        if type(x) is slice:
            return hash((x.start, x.stop, x.step))
        raise TypeError("Hashing not covered for " + str(x))


def unique(seq, key=lambda x: x):
    seen = set()
    for item in seq:
        try:
            k = key(item)
        except TypeError:
            # Just yield it and hope for the best, since we can't efficiently
            # check if we've seen it before.
            yield item
            continue
        if not isinstance(k, Hashable):
            # Just yield it and hope for the best, since we can't efficiently
            # check if we've seen it before.
            yield item
        elif k not in seen:
            seen.add(key(item))
            yield item


def interleave(seqs, pass_exceptions=()):
    iters = map(iter, seqs)
    while iters:
        newiters = []
        for itr in iters:
            try:
                yield next(itr)
                newiters.append(itr)
            except (StopIteration,) + tuple(pass_exceptions):
                pass
        iters = newiters


def take(n, seq):
    if n is None:
        return seq
    if n == 0:
        return tuple(seq)
    return tuple(islice(seq, 0, n))


def evalt(t):
    """Evaluate a tuple if unevaluated.

    >>> from kanren.util import evalt
    >>> add = lambda x, y: x + y
    >>> evalt((add, 2, 3))
    5
    >>> evalt(add(2, 3))
    5
    """

    if isinstance(t, tuple) and len(t) >= 1 and callable(t[0]):
        return t[0](*t[1:])
    else:
        return t


def intersection(*seqs):
    return (item for item in seqs[0] if all(item in seq for seq in seqs[1:]))


def groupsizes(total, len):
    """Construct groups of length len that add up to total.

    >>> from kanren.util import groupsizes
    >>> tuple(groupsizes(4, 2))
    ((1, 3), (2, 2), (3, 1))
    """
    if len == 1:
        yield (total,)
    else:
        for i in range(1, total - len + 1 + 1):
            for perm in groupsizes(total - i, len - 1):
                yield (i,) + perm


def pprint(g):  # pragma: no cover
    """Pretty print a tree of goals."""
    if callable(g) and hasattr(g, "__name__"):
        return g.__name__
    if isinstance(g, type):
        return g.__name__
    if isinstance(g, tuple):
        return "(" + ", ".join(map(pprint, g)) + ")"
    return str(g)


def index(tup, ind):
    """Fancy indexing with tuples."""
    return tuple(tup[i] for i in ind)
