from pytest import raises

from kanren.util import (
    FlexibleSet,
    dicthash,
    groupsizes,
    hashable,
    intersection,
    multihash,
    unique,
)


def test_hashable():
    assert hashable(2)
    assert hashable((2, 3))
    assert not hashable({1: 2})
    assert not hashable((1, {2: 3}))


def test_unique():
    assert tuple(unique((1, 2, 3))) == (1, 2, 3)
    assert tuple(unique((1, 2, 1, 3))) == (1, 2, 3)


def test_unique_dict():
    assert tuple(unique(({1: 2}, {2: 3}), key=dicthash)) == ({1: 2}, {2: 3})
    assert tuple(unique(({1: 2}, {1: 2}), key=dicthash)) == ({1: 2},)


def test_unique_not_hashable():
    assert tuple(unique(([1], [1])))


def test_multihash():
    inputs = 2, (1, 2), [1, 2], {1: 2}, (1, [2]), slice(1, 2)
    assert all(isinstance(multihash(i), int) for i in inputs)


def test_intersection():
    a, b, c = (1, 2, 3, 4), (2, 3, 4, 5), (3, 4, 5, 6)

    assert tuple(intersection(a, b, c)) == (3, 4)


def test_groupsizes():
    assert set(groupsizes(4, 2)) == set(((1, 3), (2, 2), (3, 1)))
    assert set(groupsizes(5, 2)) == set(((1, 4), (2, 3), (3, 2), (4, 1)))
    assert set(groupsizes(4, 1)) == set([(4,)])
    assert set(groupsizes(4, 4)) == set([(1, 1, 1, 1)])


def test_flexibleset():

    test_set = set([1, 2, 4])
    test_fs = FlexibleSet([1, 2, 4])

    assert test_fs.set == test_set
    assert test_fs.list == []

    test_fs.discard(3)
    test_set.discard(3)

    assert test_fs == test_set

    test_fs.discard(2)
    test_set.discard(2)

    with raises(KeyError):
        test_set.remove(3)
    with raises(KeyError):
        test_fs.remove(3)

    res_fs = test_fs.pop()
    res_set = test_set.pop()

    assert res_fs == res_set and test_fs == test_set

    test_fs_2 = FlexibleSet([1, 2, [3, 4], {"a"}])
    assert len(test_fs_2) == 4
    assert test_fs_2.set == {1, 2}
    assert test_fs_2.list == [[3, 4], {"a"}]

    test_fs_2.add(2)
    test_fs_2.add([3, 4])
    test_fs_2.add({"a"})
    assert test_fs_2.set == {1, 2}
    assert test_fs_2.list == [[3, 4], {"a"}]

    assert 1 in test_fs_2
    assert {"a"} in test_fs_2
    assert [3, 4] in test_fs_2

    assert test_fs_2 != test_set

    test_fs_2.discard(3)
    test_fs_2.discard([3, 4])

    assert test_fs_2.set == {1, 2}
    assert test_fs_2.list == [{"a"}]

    with raises(KeyError):
        test_fs_2.remove(3)
    with raises(KeyError):
        test_fs_2.remove([1, 4])

    test_fs_2.remove({"a"})

    assert test_fs_2.set == {1, 2}
    assert test_fs_2.list == []

    test_fs_2.add([5])
    pop_var = test_fs_2.pop()
    assert pop_var not in test_fs_2.set
    assert test_fs_2.list == [[5]]
    pop_var = test_fs_2.pop()
    assert test_fs_2.set == set()
    assert test_fs_2.list == [[5]]
    assert [5] == test_fs_2.pop()
    assert test_fs_2.set == set()
    assert test_fs_2.list == []

    with raises(KeyError):
        test_fs_2.pop()

    assert FlexibleSet([1, 2, [3, 4], {"a"}]) == FlexibleSet([1, 2, [3, 4], {"a"}])
    assert FlexibleSet([1, 2, [3, 4], {"a"}]) != FlexibleSet([1, [3, 4], {"a"}])

    test_fs_3 = FlexibleSet([1, 2, [3, 4], {"a"}])
    test_fs_3.clear()
    assert test_fs_3.set == set()
    assert test_fs_3.list == list()

    test_fs_3 = FlexibleSet([1, 2, [3, 4], {"a"}])
    assert repr(test_fs_3) == "FlexibleSet([1, 2, [3, 4], {'a'}])"
