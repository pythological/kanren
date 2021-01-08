from collections.abc import Iterator
from itertools import count

from cons import cons
from pytest import raises
from unification import var

from kanren.core import (
    conde,
    eq,
    fail,
    ground_order,
    ifa,
    lall,
    lany,
    lconj,
    lconj_seq,
    ldisj,
    ldisj_seq,
    run,
    succeed,
)


def results(g, s=None):
    if s is None:
        s = dict()
    return tuple(g(s))


def test_eq():
    x = var()
    assert tuple(eq(x, 2)({})) == ({x: 2},)
    assert tuple(eq(x, 2)({x: 3})) == ()


def test_lconj_basics():

    a, b = var(), var()
    res = list(lconj(eq(1, a), eq(2, b))({}))
    assert res == [{a: 1, b: 2}]

    res = list(lconj(eq(1, a))({}))
    assert res == [{a: 1}]

    res = list(lconj_seq([])({}))
    assert res == [{}]

    res = list(lconj(eq(1, a), eq(2, a))({}))
    assert res == []

    res = list(lconj(eq(1, 2))({}))
    assert res == []

    res = list(lconj(eq(1, 1))({}))
    assert res == [{}]

    def gen():
        for i in [succeed, succeed]:
            yield i

    res = list(lconj(gen())({}))
    assert res == [{}]

    def gen():
        return

    res = list(lconj_seq([gen()])({}))
    assert res == []


def test_ldisj_basics():

    a = var()
    res = list(ldisj(eq(1, a))({}))
    assert res == [{a: 1}]

    res = list(ldisj(eq(1, 2))({}))
    assert res == []

    res = list(ldisj(eq(1, 1))({}))
    assert res == [{}]

    res = list(ldisj(eq(1, a), eq(1, a))({}))
    assert res == [{a: 1}, {a: 1}]

    res = list(ldisj(eq(1, a), eq(2, a))({}))
    assert res == [{a: 1}, {a: 2}]

    res = list(ldisj_seq([])({}))
    assert res == [{}]

    def gen():
        for i in [succeed, succeed]:
            yield i

    res = list(ldisj(gen())({}))
    assert res == [{}, {}]


def test_conde_basics():

    a, b = var(), var()
    res = list(conde([eq(1, a), eq(2, b)], [eq(1, b), eq(2, a)])({}))
    assert res == [{a: 1, b: 2}, {b: 1, a: 2}]

    res = list(conde([eq(1, a), eq(2, 1)], [eq(1, b), eq(2, a)])({}))
    assert res == [{b: 1, a: 2}]

    aa, ab, ba, bb, bc = var(), var(), var(), var(), var()
    res = list(
        conde(
            [eq(1, a), conde([eq(11, aa)], [eq(12, ab)])],
            [
                eq(1, b),
                conde([eq(111, ba), eq(112, bb)], [eq(121, bc)]),
            ],
        )({})
    )
    assert res == [
        {a: 1, aa: 11},
        {b: 1, ba: 111, bb: 112},
        {a: 1, ab: 12},
        {b: 1, bc: 121},
    ]

    res = list(conde([eq(1, 2)], [eq(1, 1)])({}))
    assert res == [{}]

    assert list(lconj(eq(1, 1))({})) == [{}]

    res = list(lconj(conde([eq(1, 2)], [eq(1, 1)]))({}))
    assert res == [{}]

    res = list(lconj(conde([eq(1, 2)], [eq(1, 1)]), conde([eq(1, 2)], [eq(1, 1)]))({}))
    assert res == [{}]


def test_lany():
    x = var()
    assert len(tuple(lany(eq(x, 2), eq(x, 3))({}))) == 2
    assert len(tuple(lany(eq(x, 2), eq(x, 3))({}))) == 2


def test_lall():
    x = var()
    assert results(lall(eq(x, 2))) == ({x: 2},)
    assert results(lall(eq(x, 2), eq(x, 3))) == ()
    assert results(lall()) == ({},)
    assert run(0, x, lall()) == (x,)


def test_conde():
    x = var()
    assert results(conde([eq(x, 2)], [eq(x, 3)])) == ({x: 2}, {x: 3})
    assert results(conde([eq(x, 2), eq(x, 3)])) == ()

    assert set(run(0, x, conde([eq(x, 2)], [eq(x, 3)]))) == {2, 3}
    assert set(run(0, x, conde([eq(x, 2), eq(x, 3)]))) == set()

    goals = ([eq(x, i)] for i in count())  # infinite number of goals
    assert run(1, x, conde(goals)) == (0,)
    assert run(1, x, conde(goals)) == (1,)


def test_short_circuit():
    def badgoal(s):
        raise NotImplementedError()

    x = var("x")
    tuple(run(5, x, fail, badgoal))  # Does not raise exception


def test_run():
    x, y, z = var(), var(), var()
    res = run(None, x, eq(x, 1))
    assert isinstance(res, Iterator)
    assert tuple(res) == (1,)
    assert run(1, x, eq(x, 1)) == (1,)
    assert run(2, x, eq(x, 1)) == (1,)
    assert run(0, x, eq(x, 1)) == (1,)
    assert run(1, x, eq(x, (y, z)), eq(y, 3), eq(z, 4)) == ((3, 4),)
    assert set(run(2, x, conde([eq(x, 1)], [eq(x, 2)]))) == set((1, 2))


def test_run_output_reify():
    x = var()
    assert run(0, (1, 2, x), eq(x, 3)) == ((1, 2, 3),)


def test_lanyseq():
    x = var()
    g = lany((eq(x, i) for i in range(3)))
    assert list(g({})) == [{x: 0}, {x: 1}, {x: 2}]
    assert list(g({})) == [{x: 0}, {x: 1}, {x: 2}]

    # Test lanyseq with an infinite number of goals.
    assert set(run(3, x, lany((eq(x, i) for i in count())))) == {0, 1, 2}
    assert set(run(3, x, lany((eq(x, i) for i in count())))) == {0, 1, 2}


def test_lall_errors():
    class SomeException(Exception):
        pass

    def bad_relation():
        def _bad_relation(s):
            raise SomeException("some exception")

        return lall(_bad_relation)

    with raises(SomeException):
        run(0, var(), bad_relation())


def test_dict():
    x = var()
    assert run(0, x, eq({1: x}, {1: 2})) == (2,)


def test_ifa():
    x, y = var(), var()

    assert run(0, (x, y), ifa(lall(eq(x, True), eq(y, 1)), eq(y, 2))) == ((True, 1),)
    assert run(
        0, y, eq(x, False), ifa(lall(eq(x, True), eq(y, 1)), lall(eq(y, 2)))
    ) == (2,)
    assert (
        run(
            0,
            y,
            eq(x, False),
            ifa(lall(eq(x, True), eq(y, 1)), lall(eq(x, True), eq(y, 2))),
        )
        == ()
    )

    assert (
        run(
            0,
            y,
            eq(x, True),
            ifa(lall(eq(x, True), eq(y, 1)), lall(eq(x, True), eq(y, 2))),
        )
        == (1,)
    )


def test_ground_order():
    x, y, z = var(), var(), var()
    assert run(0, x, ground_order((y, [1, z], 1), x)) == ([1, [1, z], y],)
    a, b, c = var(), var(), var()
    assert run(0, (a, b, c), ground_order((y, [1, z], 1), (a, b, c))) == (
        (1, [1, z], y),
    )
    res = run(0, z, ground_order([cons(x, y), (x, y)], z))
    assert res == ([(x, y), cons(x, y)],)
    res = run(0, z, ground_order([(x, y), cons(x, y)], z))
    assert res == ([(x, y), cons(x, y)],)
