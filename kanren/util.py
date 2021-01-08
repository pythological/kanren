from collections import namedtuple
from collections.abc import Hashable, Iterable, Mapping, MutableSet, Set
from itertools import chain

HashableForm = namedtuple("HashableForm", ["type", "data"])


class FlexibleSet(MutableSet):
    """A set that uses a list (and costly identity check) for unhashable items."""

    __slots__ = ("set", "list")

    def __init__(self, iterable=None):

        self.set = set()
        self.list = []

        if iterable is not None:
            for i in iterable:
                self.add(i)

    def add(self, item):
        try:
            self.set.add(item)
        except TypeError:
            # TODO: Could try `make_hashable`.
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

    def copy(self):
        res = type(self)()
        res.set = self.set.copy()
        res.list = self.list.copy()
        return res

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


def make_hashable(x):
    # TODO: Better as a dispatch function?
    if hashable(x):
        return x
    if isinstance(x, slice):
        return HashableForm(type(x), (x.start, x.stop, x.step))
    if isinstance(x, Mapping):
        return HashableForm(type(x), frozenset(tuple(multihash(i) for i in x.items())))
    if isinstance(x, Iterable):
        return HashableForm(type(x), tuple(multihash(i) for i in x))
    raise TypeError(f"Hashing not covered for {x}")


def multihash(x):
    return hash(make_hashable(x))


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
