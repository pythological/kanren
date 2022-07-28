from collections.abc import Sequence
from functools import partial, reduce
from itertools import tee
from operator import length_hint
from typing import (
    Any,
    Callable,
    Iterable,
    Iterator,
    MutableMapping,
    Optional,
    Tuple,
    Union,
    cast,
)

from cons.core import ConsPair
from toolz import interleave, take
from typing_extensions import Literal
from unification import isvar, reify, unify
from unification.core import isground


StateType = Union[MutableMapping, Literal[False]]
StateStreamType = Iterator[StateType]
GoalType = Callable[[StateType], StateStreamType]


def fail(s: StateType) -> Iterator[StateType]:
    return iter(())


def succeed(s: StateType) -> Iterator[StateType]:
    return iter((s,))


def eq(u: Any, v: Any) -> GoalType:
    """Construct a goal stating that its arguments must unify.

    See Also
    --------
        unify
    """

    def eq_goal(s: StateType) -> StateStreamType:
        s = unify(u, v, s)
        if s is not False:
            return iter((s,))
        else:
            return iter(())

    return eq_goal


def ldisj_seq(goals: Iterable[GoalType]) -> GoalType:
    """Produce a goal that returns the appended state stream from all successful goal arguments.

    In other words, it behaves like logical disjunction/OR for goals.
    """  # noqa: E501

    if length_hint(goals, -1) == 0:
        return succeed

    assert isinstance(goals, Iterable)

    def ldisj_seq_goal(S: StateType) -> StateStreamType:
        nonlocal goals

        goals, _goals = tee(goals)

        yield from interleave(g(S) for g in _goals)

    return ldisj_seq_goal


def bind(z: StateStreamType, g: GoalType) -> StateStreamType:
    """Apply a goal to a state stream and then combine the resulting state streams."""
    # We could also use `chain`, but `interleave` preserves the old behavior.
    # return chain.from_iterable(map(g, z))
    return cast(StateStreamType, interleave(map(g, z)))


def lconj_seq(goals: Iterable[GoalType]) -> GoalType:
    """Produce a goal that returns the appended state stream in which all goals are necessarily successful.

    In other words, it behaves like logical conjunction/AND for goals.
    """  # noqa: E501

    if length_hint(goals, -1) == 0:
        return succeed

    assert isinstance(goals, Iterable)

    def lconj_seq_goal(S: StateType) -> StateStreamType:
        nonlocal goals

        goals, _goals = tee(goals)

        g0 = next(_goals, None)

        if g0 is None:
            return

        yield from reduce(bind, _goals, g0(S))

    return lconj_seq_goal


def ldisj(*goals: Union[GoalType, Iterable[GoalType]]) -> GoalType:
    """Form a disjunction of goals."""
    if len(goals) == 1 and isinstance(goals[0], Iterable):
        return ldisj_seq(goals[0])

    return ldisj_seq(cast(Tuple[GoalType, ...], goals))


def lconj(*goals: Union[GoalType, Iterable[GoalType]]) -> GoalType:
    """Form a conjunction of goals."""
    if len(goals) == 1 and isinstance(goals[0], Iterable):
        return lconj_seq(goals[0])

    return lconj_seq(cast(Tuple[GoalType, ...], goals))


def conde(
    *goals: Union[Iterable[GoalType], Iterator[Iterable[GoalType]]]
) -> Union[GoalType, StateStreamType]:
    """Form a disjunction of goal conjunctions."""
    if len(goals) == 1 and isinstance(goals[0], Iterator):
        return ldisj_seq(
            lconj_seq(g) for g in cast(Iterator[Iterable[GoalType]], goals[0])
        )

    return ldisj_seq(lconj_seq(g) for g in cast(Tuple[Iterable[GoalType], ...], goals))


lall = lconj
lany = ldisj


def ground_order_key(S: StateType, x: Any) -> Literal[-1, 0, 1, 2]:
    if isvar(x):
        return 2
    elif isground(x, S):
        return -1
    elif issubclass(type(x), ConsPair):
        return 1
    else:
        return 0


def ground_order(in_args: Any, out_args: Any) -> GoalType:
    """Construct a non-relational goal that orders a list of terms based on groundedness (grounded precede ungrounded)."""  # noqa: E501

    def ground_order_goal(S: StateType) -> StateStreamType:
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


def ifa(g1: GoalType, g2: GoalType) -> GoalType:
    """Create a goal operator that returns the first stream unless it fails."""

    def ifa_goal(S: StateType) -> StateStreamType:
        g1_stream = g1(S)
        S_new = next(g1_stream, None)

        if S_new is None:
            yield from g2(S)
        else:
            yield S_new
            yield from g1_stream

    return ifa_goal


def Zzz(gctor: Callable[[Any], GoalType], *args, **kwargs) -> GoalType:
    """Create an inverse-η-delay for a goal."""

    def Zzz_goal(S: StateType) -> StateStreamType:
        yield from gctor(*args, **kwargs)(S)

    return Zzz_goal


def run(
    n: Union[None, int],
    x: Any,
    *goals: GoalType,
    results_filter: Optional[Callable[[Iterator[Any]], Any]] = None
) -> Union[Tuple[Any, ...], Iterator[Any]]:
    """Run a logic program and obtain `n` solutions that satisfy the given goals.

    >>> from kanren import run, var, eq
    >>> x = var()
    >>> run(1, x, eq(x, 1))
    (1,)

    Parameters
    ----------
    n
        The number of desired solutions. ``n=0`` returns a tuple with all
        results and ``n=None`` returns a lazy sequence of all results.
    x
        The form to reify and return.  Usually contains logic variables used in
        the given goals.
    goals
        A sequence of goals that must be true in logical conjunction
        (i.e. `lall`).
    results_filter
        A function to apply to the results stream (e.g. a `unique` filter).

    Returns
    -------
    Either an iterable or tuple of reified `x` values that satisfy the goals.

    """
    g = lall(*goals)
    results = map(partial(reify, x), g({}))

    if results_filter is not None:
        results = results_filter(results)

    if n is None:
        return results
    elif n == 0:
        return tuple(results)
    else:
        return tuple(take(n, results))


def dbgo(*args: Any, msg: Optional[Any] = None) -> GoalType:  # pragma: no cover
    """Construct a goal that sets a debug trace and prints reified arguments."""
    from pprint import pprint

    def dbgo_goal(S: StateType) -> StateStreamType:
        nonlocal args
        args = reify(args, S)

        if msg is not None:
            print(msg)

        pprint(args)

        import pdb

        pdb.set_trace()
        yield S

    return dbgo_goal
