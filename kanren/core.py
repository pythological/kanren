from statistics import mean
from itertools import tee
from operator import length_hint
from functools import partial, reduce
from collections.abc import Sequence, Generator, Mapping

from multipledispatch import dispatch

from cons.core import ConsPair, car, cdr
from unification import reify, unify, isvar

from toolz import interleave, take


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

    def eq_goal(s):
        s = unify(u, v, s)
        if s is not False:
            return iter((s,))
        else:
            return iter(())

    return eq_goal


def ldisj_seq(goals):
    """Produce a goal that returns the appended state stream from all successful goal arguments.

    In other words, it behaves like logical disjunction/OR for goals.
    """

    if length_hint(goals, -1) == 0:
        return succeed

    def ldisj_seq_goal(S):
        nonlocal goals

        goals, _goals = tee(goals)

        yield from interleave(g(S) for g in _goals)

    return ldisj_seq_goal


def bind(z, g):
    """Apply a goal to a state stream and then combine the resulting state streams."""
    # We could also use `chain`, but `interleave` preserves the old behavior.
    # return chain.from_iterable(map(g, z))
    return interleave(map(g, z))


def lconj_seq(goals):
    """Produce a goal that returns the appended state stream in which all goals are necessarily successful.

    In other words, it behaves like logical conjunction/AND for goals.
    """

    if length_hint(goals, -1) == 0:
        return succeed

    def lconj_seq_goal(S):
        nonlocal goals

        goals, _goals = tee(goals)

        g0 = next(_goals, None)

        if g0 is None:
            return

        yield from reduce(bind, _goals, g0(S))

    return lconj_seq_goal


def ldisj(*goals):
    """Form a disjunction of goals."""
    if len(goals) == 1 and isinstance(goals[0], Generator):
        goals = goals[0]

    return ldisj_seq(goals)


def lconj(*goals):
    """Form a conjunction of goals."""
    if len(goals) == 1 and isinstance(goals[0], Generator):
        goals = goals[0]

    return lconj_seq(goals)


def conde(*goals):
    """Form a disjunction of goal conjunctions."""
    if len(goals) == 1 and isinstance(goals[0], Generator):
        goals = goals[0]

    return ldisj_seq(lconj_seq(g) for g in goals)


lall = lconj
lany = ldisj


@dispatch(Mapping, object)
def shallow_ground_order_key(S, x):
    if isvar(x):
        return 10
    elif isinstance(x, ConsPair):
        val = 0
        val += 1 if isvar(car(x)) else 0
        cdr_x = cdr(x)
        if issubclass(type(x), ConsPair):
            val += 2 if isvar(cdr_x) else 0
        elif len(cdr_x) == 1:
            val += 1 if isvar(cdr_x[0]) else 0
        elif len(cdr_x) > 1:
            val += mean(1.0 if isvar(i) else 0.0 for i in cdr_x)
        return val
    return 0


def ground_order(in_args, out_args, key_fn=shallow_ground_order_key):
    """Construct a non-relational goal that orders a list of terms based on groundedness (grounded precede ungrounded)."""

    def ground_order_goal(S):
        nonlocal in_args, out_args

        in_args_rf, out_args_rf = reify((in_args, out_args), S)

        S_new = unify(
            list(out_args_rf) if isinstance(out_args_rf, Sequence) else out_args_rf,
            sorted(in_args_rf, key=partial(key_fn, S)),
            S,
        )

        if S_new is not False:
            yield S_new

    return ground_order_goal


def ground_order_seqs(in_seqs, out_seqs, key_fn=shallow_ground_order_key):
    """Construct a non-relational goal that orders lists of sequences based on the groundedness of their corresponding terms.

    >>> from unification import var
    >>> x, y = var('x'), var('y')
    >>> a, b = var('a'), var('b')
    >>> run(0, (x, y), ground_order_seqs([(a, b), (b, 2)], [x, y]))
    (((~b, ~a), (2, ~b)),)
    """

    def ground_order_seqs_goal(S):
        nonlocal in_seqs, out_seqs, key_fn

        in_seqs_rf, out_seqs_rf = reify((in_seqs, out_seqs), S)

        if (
            not any(isinstance(s, str) for s in in_seqs_rf)
            and reduce(
                lambda x, y: x == y and y, (length_hint(s, -1) for s in in_seqs_rf)
            )
            > 0
        ):

            in_seqs_ord = zip(*sorted(zip(*in_seqs_rf), key=partial(key_fn, S)))
            S_new = unify(list(out_seqs_rf), list(in_seqs_ord), S)

            if S_new is not False:
                yield S_new
        else:

            S_new = unify(out_seqs_rf, in_seqs_rf, S)

            if S_new is not False:
                yield S_new

    return ground_order_seqs_goal


def ifa(g1, g2):
    """Create a goal operator that returns the first stream unless it fails."""

    def ifa_goal(S):
        g1_stream = g1(S)
        S_new = next(g1_stream, None)

        if S_new is None:
            yield from g2(S)
        else:
            yield S_new
            yield from g1_stream

    return ifa_goal


def Zzz(gctor, *args, **kwargs):
    """Create an inverse-η-delay for a goal."""

    def Zzz_goal(S):
        yield from gctor(*args, **kwargs)(S)

    return Zzz_goal


def run(n, x, *goals, results_filter=None):
    """Run a logic program and obtain n solutions that satisfy the given goals.

    >>> from kanren import run, var, eq
    >>> x = var()
    >>> run(1, x, eq(x, 1))
    (1,)

    Parameters
    ----------
    n: int
        The number of desired solutions. `n=0` returns a tuple
        with all results and `n=None` returns a lazy sequence of all results.
    x: object
        The form to reify and output.  Usually contains logic variables used in
        the given goals.
    goals: Callables
        A sequence of goals that must be true in logical conjunction
        (i.e. `lall`).
    results_filter: Callable
        A function to apply to the results stream (e.g. a `unique` filter).
    """
    results = map(partial(reify, x), lall(*goals)({}))

    if results_filter is not None:
        results = results_filter(results)

    if n is None:
        return results
    elif n == 0:
        return tuple(results)
    else:
        return tuple(take(n, results))


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
