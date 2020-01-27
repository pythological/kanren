from itertools import count

from pytest import raises, mark

from unification import var, isvar

from kanren.core import (
    run,
    fail,
    eq,
    conde,
    goaleval,
    lany,
    lallgreedy,
    lanyseq,
    earlyorder,
    EarlyGoalError,
    lall,
    earlysafe,
    lallfirst,
    condeseq,
    ifa,
)
from kanren.util import evalt


def ege_membero(x, coll):
    if not isvar(coll):
        return (lany,) + tuple((eq, x, item) for item in coll)
    raise EarlyGoalError()


def test_eq():
    x = var("x")
    assert tuple(eq(x, 2)({})) == ({x: 2},)
    assert tuple(eq(x, 2)({x: 3})) == ()


def test_lany():
    x = var("x")
    assert len(tuple(lany(eq(x, 2), eq(x, 3))({}))) == 2
    assert len(tuple(lany((eq, x, 2), (eq, x, 3))({}))) == 2

    g = lany(ege_membero(x, (1, 2, 3)), ege_membero(x, (2, 3, 4)))
    assert tuple(g({})) == ({x: 1}, {x: 2}, {x: 3}, {x: 4})


def test_lallfirst():
    x = var("x")
    g = lallfirst(ege_membero(x, (1, 2, 3)), ege_membero(x, (2, 3, 4)))
    assert tuple(g({})) == ({x: 2}, {x: 3})
    assert tuple(lallfirst()({})) == ({},)


def test_lallgreedy():
    x, y = var("x"), var("y")
    assert run(0, x, lallgreedy((eq, y, set([1]))), (ege_membero, x, y)) == (1,)
    with raises(EarlyGoalError):
        run(0, x, lallgreedy((ege_membero, x, y), (eq, y, {1})))


@mark.parametrize("lall_impl", [lallgreedy, lall, lallfirst])
def test_lall(lall_impl):
    """Test that all three implementations of lallgreedy behave identically for correctly ordered goals."""
    x, y = var("x"), var("y")
    assert results(lall_impl((eq, x, 2))) == ({x: 2},)
    assert results(lall_impl((eq, x, 2), (eq, x, 3))) == ()
    assert results(lall_impl()) == ({},)

    assert run(0, x, lall_impl((eq, y, (1, 2)), (ege_membero, x, y)))
    assert run(0, x, lall_impl()) == (x,)
    with raises(EarlyGoalError):
        run(0, x, lall_impl(ege_membero(x, y)))


@mark.parametrize("lall_impl", [lall, lallfirst])
def test_safe_reordering_lall(lall_impl):
    x, y = var("x"), var("y")
    assert run(0, x, lall_impl((ege_membero, x, y), (eq, y, (1, 2)))) == (1, 2)


def test_earlysafe():
    x, y = var("x"), var("y")
    assert earlysafe((eq, 2, 2))
    assert earlysafe((eq, 2, 3))
    assert earlysafe((ege_membero, x, (1, 2, 3)))
    assert not earlysafe((ege_membero, x, y))


def test_earlyorder():
    x, y = var(), var()
    assert earlyorder((eq, 2, x)) == ((eq, 2, x),)
    assert earlyorder((eq, 2, x), (eq, 3, x)) == ((eq, 2, x), (eq, 3, x))
    assert earlyorder((ege_membero, x, y), (eq, y, (1, 2, 3)))[0] == (eq, y, (1, 2, 3))


def test_conde():
    x = var("x")
    assert results(conde([eq(x, 2)], [eq(x, 3)])) == ({x: 2}, {x: 3})
    assert results(conde([eq(x, 2), eq(x, 3)])) == ()


def test_condeseq():
    x = var("x")
    assert set(run(0, x, condeseq(([eq(x, 2)], [eq(x, 3)])))) == {2, 3}
    assert set(run(0, x, condeseq([[eq(x, 2), eq(x, 3)]]))) == set()

    goals = ([eq(x, i)] for i in count())  # infinite number of goals
    assert run(1, x, condeseq(goals)) == (0,)
    assert run(1, x, condeseq(goals)) == (1,)


def test_short_circuit():
    def badgoal(s):
        raise NotImplementedError()

    x = var("x")
    tuple(run(5, x, fail, badgoal))  # Does not raise exception


def test_run():
    x, y, z = map(var, "xyz")
    assert run(1, x, eq(x, 1)) == (1,)
    assert run(2, x, eq(x, 1)) == (1,)
    assert run(0, x, eq(x, 1)) == (1,)
    assert run(1, x, eq(x, (y, z)), eq(y, 3), eq(z, 4)) == ((3, 4),)
    assert set(run(2, x, conde([eq(x, 1)], [eq(x, 2)]))) == set((1, 2))


def test_run_output_reify():
    x = var()
    assert run(0, (1, 2, x), eq(x, 3)) == ((1, 2, 3),)


def test_lanyseq():
    x = var("x")
    g = lanyseq(((eq, x, i) for i in range(3)))
    assert list(goaleval(g)({})) == [{x: 0}, {x: 1}, {x: 2}]
    assert list(goaleval(g)({})) == [{x: 0}, {x: 1}, {x: 2}]

    # Test lanyseq with an infinite number of goals.
    assert set(run(3, x, lanyseq(((eq, x, i) for i in count())))) == {0, 1, 2}
    assert set(run(3, x, (lanyseq, ((eq, x, i) for i in count())))) == {0, 1, 2}


def test_evalt():
    add = lambda x, y: x + y
    assert evalt((add, 2, 3)) == 5
    assert evalt(add(2, 3)) == 5
    assert evalt((1, 2)) == (1, 2)


def test_goaleval():
    x, y = var("x"), var("y")
    g = eq(x, 2)
    assert goaleval(g) == g
    assert callable(goaleval((eq, x, 2)))
    with raises(EarlyGoalError):
        goaleval((ege_membero, x, y))
    assert callable(goaleval((lallgreedy, (eq, x, 2))))


def test_lall_errors():
    """Make sure we report the originating exception when it isn't just an
    `EarlyGoalError`.
    """

    class SomeException(Exception):
        pass

    def bad_relation():
        def _bad_relation():
            raise SomeException("some exception")

        return (lall, (_bad_relation,))

    with raises(SomeException):
        run(0, var(), (bad_relation,))


def test_lany_is_early_safe():
    x, y = var(), var()
    assert run(0, x, lany((ege_membero, x, y), (eq, x, 2))) == (2,)


def results(g, s=None):
    if s is None:
        s = dict()
    return tuple(goaleval(g)(s))


def test_dict():
    x = var()
    assert run(0, x, eq({1: x}, {1: 2})) == (2,)


def test_goal_ordering():
    # Regression test for https://github.com/logpy/logpy/issues/58

    def lefto(q, p, lst):
        if isvar(lst):
            raise EarlyGoalError()
        return ege_membero((q, p), zip(lst, lst[1:]))

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

    assert run(
        0,
        y,
        eq(x, True),
        ifa(lall(eq(x, True), eq(y, 1)), lall(eq(x, True), eq(y, 2))),
    ) == (1,)
