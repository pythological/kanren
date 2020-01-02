import pytest

from unification import var, isvar, unify

from cons import cons

from kanren.goals import (
    tailo,
    heado,
    appendo,
    seteq,
    conso,
    nullo,
    itero,
    permuteq,
    membero,
    rembero,
)
from kanren.core import run, eq, goaleval, lall, lallgreedy, EarlyGoalError

x, y, z, w = var("x"), var("y"), var("z"), var("w")


def results(g, s=None):
    if s is None:
        s = dict()
    return tuple(goaleval(g)(s))


def test_heado():
    assert (x, 1) in results(heado(x, (1, 2, 3)))[0].items()
    assert (x, 1) in results(heado(1, (x, 2, 3)))[0].items()
    assert results(heado(x, ())) == ()

    assert run(0, x, (heado, x, z), (conso, 1, y, z)) == (1,)


def test_tailo():
    assert (x, (2, 3)) in results((tailo, x, (1, 2, 3)))[0].items()
    assert (x, ()) in results((tailo, x, (1,)))[0].items()
    assert results((tailo, x, ())) == ()

    assert run(0, y, (tailo, y, z), (conso, x, (1, 2), z)) == ((1, 2),)


def test_conso():
    assert not results(conso(x, y, ()))
    assert results(conso(1, (2, 3), (1, 2, 3)))
    assert results(conso(x, (2, 3), (1, 2, 3))) == ({x: 1},)
    assert results(conso(1, (2, 3), x)) == ({x: (1, 2, 3)},)
    assert results(conso(x, y, (1, 2, 3))) == ({x: 1, y: (2, 3)},)
    assert results(conso(x, (2, 3), y)) == ({y: (x, 2, 3)},)
    assert run(0, x, conso(x, y, z), eq(z, (1, 2, 3))) == (1,)

    # Confirm that custom types are preserved.
    class mytuple(tuple):
        def __add__(self, other):
            return type(self)(super(mytuple, self).__add__(other))

    assert type(results(conso(x, mytuple((2, 3)), y))[0][y]) == mytuple


def test_nullo_itero():

    q_lv, a_lv = var(), var()

    assert run(0, q_lv, conso(1, q_lv, [1]), nullo(q_lv))
    assert run(0, q_lv, nullo(q_lv), conso(1, q_lv, [1]))

    assert not run(0, q_lv, nullo(q_lv, [], ()))
    assert run(0, [a_lv, q_lv], nullo(q_lv, a_lv, default_ConsNull=tuple)) == (
        [(), ()],
    )
    assert run(0, [a_lv, q_lv], nullo(a_lv, [], q_lv)) == ([[], []],)

    assert ([],) == run(0, q_lv, nullo(q_lv, []))
    assert ([],) == run(0, q_lv, nullo([], q_lv))
    assert (None,) == run(0, q_lv, nullo(None, q_lv))
    assert (tuple(),) == run(0, q_lv, nullo(tuple(), q_lv))
    assert (q_lv,) == run(0, q_lv, nullo(tuple(), tuple()))
    assert ([],) == run(0, q_lv, nullo(var(), q_lv))
    assert ([],) == run(0, q_lv, nullo(q_lv, var()))
    assert ([],) == run(0, q_lv, nullo(q_lv, q_lv))

    assert isvar(run(0, y, nullo([]))[0])
    assert isvar(run(0, y, nullo(None))[0])
    assert run(0, y, nullo(y))[0] == []
    assert run(0, y, conso(var(), y, [1]), nullo(y))[0] == []
    assert run(0, y, conso(var(), y, (1,)), nullo(y))[0] == ()

    assert run(1, y, conso(1, x, y), itero(y))[0] == [1]
    assert run(1, y, conso(1, x, y), conso(2, z, x), itero(y))[0] == [1, 2]

    # Make sure that the remaining results end in logic variables
    res_2 = run(2, y, conso(1, x, y), conso(2, z, x), itero(y))[1]
    assert res_2[:2] == [1, 2]
    assert isvar(res_2[-1])


def test_membero():
    x = var("x")
    assert set(run(5, x, membero(x, (1, 2, 3)), membero(x, (2, 3, 4)))) == {2, 3}

    assert run(5, x, membero(2, (1, x, 3))) == (2,)
    assert run(0, x, (membero, 1, (1, 2, 3))) == (x,)
    assert run(0, x, (membero, 1, (2, 3))) == ()


def test_membero_can_be_reused():
    g = membero(x, (0, 1, 2))
    assert list(goaleval(g)({})) == [{x: 0}, {x: 1}, {x: 2}]
    assert list(goaleval(g)({})) == [{x: 0}, {x: 1}, {x: 2}]


def test_uneval_membero():
    assert set(run(100, x, (membero, y, ((1, 2, 3), (4, 5, 6))), (membero, x, y))) == {
        1,
        2,
        3,
        4,
        5,
        6,
    }


def test_seteq():
    abc = tuple("abc")
    bca = tuple("bca")
    assert results(seteq(abc, bca))
    assert len(results(seteq(abc, x))) == 6
    assert len(results(seteq(x, abc))) == 6
    assert bca in run(0, x, seteq(abc, x))
    assert results(seteq((1, 2, 3), (3, x, 1))) == ({x: 2},)

    assert run(0, (x, y), seteq((1, 2, x), (2, 3, y)))[0] == (3, 1)
    assert not run(0, (x, y), seteq((4, 5, x), (2, 3, y)))


def test_permuteq():
    assert results(permuteq((1, 2), (2, 1)))
    assert results(permuteq([1, 2], [2, 1]))
    assert results(permuteq((1, 2, 2), (2, 1, 2)))

    with pytest.raises(ValueError):
        permuteq(set((1, 2, 2)), set((2, 1, 2)))

    assert not results(permuteq((1, 2), (2, 1, 2)))
    assert not results(permuteq((1, 2, 3), (2, 1, 2)))
    assert not results(permuteq((1, 2, 1), (2, 1, 2)))
    assert not results(permuteq([1, 2, 1], (2, 1, 2)))

    assert set(run(0, x, permuteq(x, (1, 2, 2)))) == set(
        ((1, 2, 2), (2, 1, 2), (2, 2, 1))
    )


def test_appendo():
    q_lv = var()
    assert run(0, q_lv, appendo((), (1, 2), (1, 2))) == (q_lv,)
    assert run(0, q_lv, appendo((), (1, 2), 1)) == ()
    assert run(0, q_lv, appendo((), (1, 2), (1,))) == ()
    assert run(0, q_lv, appendo((1, 2), (3, 4), (1, 2, 3, 4))) == (q_lv,)
    assert run(5, q_lv, appendo((1, 2, 3), q_lv, (1, 2, 3, 4, 5))) == ((4, 5),)
    assert run(5, q_lv, appendo(q_lv, (4, 5), (1, 2, 3, 4, 5))) == ((1, 2, 3),)
    assert run(5, q_lv, appendo((1, 2, 3), (4, 5), q_lv)) == ((1, 2, 3, 4, 5),)

    q_lv, r_lv = var(), var()

    assert ([1, 2, 3, 4],) == run(0, q_lv, appendo([1, 2], [3, 4], q_lv))
    assert ([3, 4],) == run(0, q_lv, appendo([1, 2], q_lv, [1, 2, 3, 4]))
    assert ([1, 2],) == run(0, q_lv, appendo(q_lv, [3, 4], [1, 2, 3, 4]))

    expected_res = set(
        [
            ((), (1, 2, 3, 4)),
            ((1,), (2, 3, 4)),
            ((1, 2), (3, 4)),
            ((1, 2, 3), (4,)),
            ((1, 2, 3, 4), ()),
        ]
    )
    assert expected_res == set(run(0, (q_lv, r_lv), appendo(q_lv, r_lv, (1, 2, 3, 4))))

    res = run(3, (q_lv, r_lv), appendo(q_lv, [3, 4], r_lv))
    assert len(res) == 3
    assert any(len(a) > 0 and isvar(a[0]) for a, b in res)
    assert all(a + [3, 4] == b for a, b in res)

    res = run(0, (q_lv, r_lv), appendo([3, 4], q_lv, r_lv))
    assert len(res) == 2
    assert ([], [3, 4]) == res[0]
    assert all(
        type(v) == cons for v in unify((var(), cons(3, 4, var())), res[1]).values()
    )


@pytest.mark.skip("Misspecified test")
def test_appendo2():
    # XXX: This test generates goal conjunctions that are non-terminating given
    # the specified goal ordering.  More specifically, it generates
    # `lall(appendo(x, y, w), appendo(w, z, ()))`, for which the first
    # `appendo` produces an infinite stream of results and the second
    # necessarily fails for all values of the first `appendo` yielding
    # non-empty `w` unifications.
    #
    # The only reason it worked before is the `EarlyGoalError`
    # and it's implicit goal reordering, which made this case an out-of-place
    # test for a goal reordering feature that has nothing to do with `appendo`.
    # Furthermore, the `EarlyGoalError` mechanics do *not* fix this general
    # problem, and it's trivial to generate an equivalent situation in which
    # an `EarlyGoalError` is never thrown.
    #
    # In other words, it seems like a nice side effect of `EarlyGoalError`, but
    # it's actually a very costly approach that masks a bigger issue; one that
    # all miniKanren programmers need to think about when developing.

    x, y, z, w = var(), var(), var(), var()
    for t in [tuple(range(i)) for i in range(5)]:
        print(t)
        for xi, yi in run(0, (x, y), appendo(x, y, t)):
            assert xi + yi == t

        results = run(2, (x, y, z, w), appendo(x, y, w), appendo(w, z, t))
        for xi, yi, zi, wi in results:
            assert xi + yi + zi == t


def test_goal_ordering():
    # Regression test for https://github.com/logpy/logpy/issues/58

    def lefto(q, p, lst):
        if isvar(lst):
            raise EarlyGoalError()
        return membero((q, p), zip(lst, lst[1:]))

    vals = var()

    # Verify the solution can be computed when we specify the execution
    # ordering.
    rules_greedy = (
        lallgreedy,
        (eq, (var(), var()), vals),
        (lefto, "green", "white", vals),
    )

    (solution,) = run(1, vals, rules_greedy)
    assert solution == ("green", "white")

    # Verify that attempting to compute the "safe" order does not itself cause
    # the evaluation to fail.
    rules_greedy = (
        lall,
        (eq, (var(), var()), vals),
        (lefto, "green", "white", vals),
    )

    (solution,) = run(1, vals, rules_greedy)
    assert solution == ("green", "white")


def test_rembero():

    q_lv = var()
    assert ([],) == run(0, q_lv, rembero(1, [1], q_lv))
    assert ([], [1]) == run(0, q_lv, rembero(1, q_lv, []))

    expected_res = (
        [5, 1, 2, 3, 4],
        [1, 5, 2, 3, 4],
        [1, 2, 5, 3, 4],
        [1, 2, 3, 5, 4],
        [1, 2, 3, 4],
        [1, 2, 3, 4, 5],
    )
    assert expected_res == run(0, q_lv, rembero(5, q_lv, [1, 2, 3, 4]))
