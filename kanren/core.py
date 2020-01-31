from itertools import tee
from functools import partial
from collections.abc import Sequence

from toolz import groupby, map
from cons.core import ConsPair
from unification import reify, unify, isvar
from unification.core import isground

from .util import dicthash, interleave, take, multihash, unique, evalt


def fail(s):
    return iter(())


def succeed(s):
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

    Note that this may raise EarlyGoalError when the ordering of the goals is
    incorrect. It is faster than lall, but should be used with care.

    """
    if not goals:
        return succeed
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
    """Construct a logical all that runs goals one at a time."""
    if not goals:
        return succeed
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
    """Construct a logical any goal."""
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
        anygoal.goals, local_goals = tee(anygoal.goals)

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


def ground_order_key(S, x):
    if isvar(x):
        return 2
    elif isground(x, S):
        return -1
    elif issubclass(type(x), ConsPair):
        return 1
    else:
        return 0


def ground_order(in_args, out_args):
    """Construct a non-relational goal that orders a list of terms based on groundedness (grounded precede ungrounded)."""

    def ground_order_goal(S):
        nonlocal in_args, out_args

        in_args_rf, out_args_rf = reify((in_args, out_args), S)

        S_new = unify(
            list(out_args_rf) if isinstance(out_args_rf, Sequence) else out_args_rf,
            sorted(in_args_rf, key=partial(ground_order_key, S)),
            S,
        )

        if S_new is not False:
            yield S_new

    return ground_order_goal


def ifa(g1, g2):
    """Create a goal operator that returns the first stream unless it fails."""

    def ifa_goal(S):
        g1_stream = goaleval(g1)(S)
        S_new = next(g1_stream, None)

        if S_new is None:
            yield from goaleval(g2)(S)
        else:
            yield S_new
            yield from g1_stream

    return ifa_goal


def Zzz(gctor, *args, **kwargs):
    """Create an inverse-η-delay for a goal."""

    def Zzz_goal(S):
        yield from goaleval(gctor(*args, **kwargs))(S)

    return Zzz_goal


def run_all(n, x, *goals, results_filter=None):
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
    if results_filter is not None:
        results = results_filter(results)
    return take(n, results)


run = partial(run_all, results_filter=partial(unique, key=multihash))


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


def dbgo(*args, msg=None):  # pragma: no cover
    """Construct a goal that sets a debug trace and prints reified arguments."""
    from pprint import pprint

    def dbgo_goal(S):
        nonlocal args
        args = reify(args, S)

        if msg is not None:
            print(msg)

        pprint(args)

        import pdb

        pdb.set_trace()
        yield S

    return dbgo_goal
