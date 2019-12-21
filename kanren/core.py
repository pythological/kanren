import itertools as it
from functools import partial
from .util import dicthash, interleave, take, multihash, unique, evalt
from toolz import groupby, map

from unification import reify, unify


def fail(s):
    return iter(())


def success(s):
    return iter((s,))


def eq(u, v):
    """Construct a goal stating that its arguments must unify.

    See Also
    --------
        unify
    """

    def goal_eq(s):
        result = unify(u, v, s)
        if result is not False:
            yield result

    return goal_eq


def lall(*goals):
    """Construct a logical all with goal reordering to avoid EarlyGoalErrors.

    See Also
    --------
        EarlyGoalError
        earlyorder

    >>> from kanren import lall, membero, var
    >>> x = var('x')
    >>> run(0, x, lall(membero(x, (1,2,3)), membero(x, (2,3,4))))
    (2, 3)
    """
    return (lallgreedy,) + tuple(earlyorder(*goals))


def lallgreedy(*goals):
    """Construct a logical all that greedily evaluates each goals in the order provided.

    Note that this may raise EarlyGoalError when the ordering of the
    goals is incorrect. It is faster than lall, but should be used
    with care.

    >>> from kanren import eq, run, membero, var
    >>> x, y = var('x'), var('y')
    >>> run(0, x, lallgreedy((eq, y, set([1]))), (membero, x, y))
    (1,)
    >>> run(0, x, lallgreedy((membero, x, y), (eq, y, {1})))  # doctest: +SKIP
    Traceback (most recent call last):
      ...
    kanren.core.EarlyGoalError
    """
    if not goals:
        return success
    if len(goals) == 1:
        return goals[0]

    def allgoal(s):
        g = goaleval(reify(goals[0], s))
        return unique(
            interleave(
                goaleval(reify((lallgreedy,) + tuple(goals[1:]), ss))(ss) for ss in g(s)
            ),
            key=dicthash,
        )

    return allgoal


def lallfirst(*goals):
    """Construct a logical all that runs goals one at a time.

    >>> from kanren import membero, var
    >>> x = var('x')
    >>> g = lallfirst(membero(x, (1,2,3)), membero(x, (2,3,4)))
    >>> tuple(g({}))
    ({~x: 2}, {~x: 3})
    >>> tuple(lallfirst()({}))
    ({},)
    """
    if not goals:
        return success
    if len(goals) == 1:
        return goals[0]

    def allgoal(s):
        for i, g in enumerate(goals):
            try:
                goal = goaleval(reify(g, s))
            except EarlyGoalError:
                continue
            other_goals = tuple(goals[:i] + goals[i + 1 :])
            return unique(
                interleave(
                    goaleval(reify((lallfirst,) + other_goals, ss))(ss)
                    for ss in goal(s)
                ),
                key=dicthash,
            )
        else:
            raise EarlyGoalError()

    return allgoal


def lany(*goals):
    """Construct a logical any goal.

    >>> from kanren import lany, membero, var
    >>> x = var('x')
    >>> g = lany(membero(x, (1,2,3)), membero(x, (2,3,4)))
    >>> tuple(g({}))
    ({~x: 1}, {~x: 2}, {~x: 3}, {~x: 4})
    """
    if len(goals) == 1:
        return goals[0]
    return lanyseq(goals)


def earlysafe(goal):
    """Check if a goal can be evaluated without raising an EarlyGoalError."""
    try:
        goaleval(goal)
        return True
    except EarlyGoalError:
        return False


def earlyorder(*goals):
    """Reorder goals to avoid EarlyGoalErrors.

    All goals are evaluated.  Those that raise EarlyGoalErrors are placed at
    the end in a lall

    See Also
    --------
        EarlyGoalError
    """
    if not goals:
        return ()
    groups = groupby(earlysafe, goals)
    good = groups.get(True, [])
    bad = groups.get(False, [])

    if not good:
        raise EarlyGoalError()
    elif not bad:
        return tuple(good)
    else:
        return tuple(good) + ((lall,) + tuple(bad),)


def conde(*goalseqs):
    """Construct a logical cond goal.

    Goal constructor to provides logical AND and OR

    conde((A, B, C), (D, E)) means (A and B and C) or (D and E)
    Equivalent to the (A, B, C); (D, E) syntax in Prolog.

    See Also
    --------
        lall - logical all
        lany - logical any
    """
    return (lany,) + tuple((lall,) + tuple(gs) for gs in goalseqs)


def lanyseq(goals):
    """Construct a logical any with a possibly infinite number of goals."""

    def anygoal(s):
        anygoal.goals, local_goals = it.tee(anygoal.goals)

        def f(goals):
            for goal in goals:
                try:
                    yield goaleval(reify(goal, s))(s)
                except EarlyGoalError:
                    pass

        return unique(
            interleave(f(local_goals), pass_exceptions=[EarlyGoalError]), key=dicthash
        )

    anygoal.goals = goals

    return anygoal


def condeseq(goalseqs):
    """Construct a goal like conde, but support generic, possibly infinite iterators of goals."""
    return (lanyseq, ((lall,) + tuple(gs) for gs in goalseqs))


def everyg(predicate, coll):
    """Assert that a predicate applies to all elements of a collection."""
    return (lall,) + tuple((predicate, x) for x in coll)


def run(n, x, *goals):
    """Run a logic program and obtain n solutions that satisfy the given goals.

    >>> from kanren import run, var, eq
    >>> x = var()
    >>> run(1, x, eq(x, 1))
    (1,)

    Parameters
    ----------
    n: int
        The number of desired solutions (see `take`). `n=0` returns a tuple
        with all results and `n=None` returns a lazy sequence of all results.
    x: object
        The form to reify and output.  Usually contains logic variables used in
        the given goals.
    goals: Callables
        A sequence of goals that must be true in logical conjunction
        (i.e. `lall`).
    """
    results = map(partial(reify, x), goaleval(lall(*goals))({}))
    return take(n, unique(results, key=multihash))


class EarlyGoalError(Exception):
    """An exception indicating that a goal has been constructed prematurely.

    Consider the following case

    >>> from kanren import run, eq, membero, var
    >>> x, coll = var(), var()
    >>> run(0, x, (membero, x, coll), (eq, coll, (1, 2, 3))) # doctest: +SKIP

    The first goal, membero, iterates over an infinite sequence of all possible
    collections.  This is unproductive.  Rather than proceed, membero raises an
    EarlyGoalError, stating that this goal has been called early.

    The goal constructor lall Logical-All-Early will reorder such goals to
    the end so that the call becomes

    >>> run(0, x, (eq, coll, (1, 2, 3)), (membero, x, coll)) # doctest: +SKIP

    In this case coll is first unified to ``(1, 2, 3)`` then x iterates over
    all elements of coll, 1, then 2, then 3.

    See Also
    --------
        lall
        earlyorder
    """


def find_fixed_point(f, arg):
    """Repeatedly calls f until a fixed point is reached.

    This may not terminate, but should if you apply some eventually-idempotent
    simplification operation like evalt.
    """
    last, cur = object(), arg
    while last != cur:
        last = cur
        cur = f(cur)
    return cur


def goaleval(goal):
    """Expand and then evaluate a goal.

    See Also
    --------
       goalexpand
    """
    if callable(goal):  # goal is already a function like eq(x, 1)
        return goal
    if isinstance(goal, tuple):  # goal is not yet evaluated like (eq, x, 1)
        return find_fixed_point(evalt, goal)
    raise TypeError("Expected either function or tuple")
