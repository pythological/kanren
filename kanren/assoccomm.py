"""Functions for associative and commutative unification.

This module provides goals for associative and commutative unification.  It
accomplishes this through naively trying all possibilities.  This was built to
be used in the computer algebra systems SymPy and Theano.

"""
from functools import partial
from operator import length_hint, eq as equal
from collections.abc import Sequence


from unification import reify, unify, var


from etuples import etuple

from .core import conde, eq, ground_order, lall, lany, succeed, Zzz, fail
from .goals import itero, permuteo, conso
from .facts import Relation
from .graph import term_walko
from .term import term, applyo, TermType, operator, arguments

associative = Relation("associative")
commutative = Relation("commutative")


def flatten_assoc_args(op_predicate, term, shallow=True):
    """Flatten/normalize a term with an associative operator.

    Parameters
    ----------
    op_predicate: callable
        A function used to determine the operators to flatten.
    items: Sequence
        The term to flatten.
    shallow: bool (optional)
        Indicate whether or not flattening should be done at all depths.
    """

    if not isinstance(term, TermType):
        return term

    def _flatten(term):
        for i in term:
            if isinstance(i, TermType) and op_predicate(operator(i)):
                i_cdr = arguments(i)
                if length_hint(i_cdr) > 0:
                    if shallow:
                        yield from iter(i_cdr)
                    else:
                        yield from _flatten(i_cdr)
                else:
                    yield i
            else:
                yield i

    term_type = type(arguments(term))
    return term_type(_flatten(term))


def partitions(in_seq, n_parts=None, min_size=1, part_fn=lambda x: x):
    """Generate all partitions of a sequence for given numbers of partitions and minimum group sizes.

    Parameters
    ----------
    in_seq: Sequence
       The sequence to be partitioned.
    n_parts: int
       Number of partitions.  `None` means all partitions in `range(2, len(in_seq))`.
    min_size: int
       The minimum size of a partition.
    part_fn: Callable
       A function applied to every partition.
    """

    def partition(seq, res):
        if (
            n_parts is None
            and
            # We don't want the original sequence
            len(res) > 0
        ) or len(res) + 1 == n_parts:
            yield type(in_seq)(res + [part_fn(seq)])

            if n_parts is not None:
                return

        for s in range(min_size, len(seq) + 1 - min_size, 1):
            yield from partition(seq[s:], res + [part_fn(seq[:s])])

    return partition(in_seq, [])


def assoc_args(rator, rands, n=None, ctor=None):
    """Produce all associative argument combinations of rator + rands in n-sized rand groupings.

    The normal/canonical form is left-associative, e.g.
        `(op, 1, 2, 3, 4) == (op, (op, (op, 1, 2), 3), 4)`

    Parameters
    ----------
    rator: object
        The operator that's assumed to be associative.
    rands: Sequence
        The operands.
    n: int (optional)
        The number of arguments in the resulting `(op,) + output` terms.
        If not specified, all argument sizes are returned.
    ctor: callable
        The constructor to use when each term is created.
        If not specified, the constructor is inferred from `type(rands)`.
    """

    if ctor is None:
        ctor = type(rands)

    if len(rands) <= 2 or n is not None and len(rands) <= n:
        yield ctor(rands)
        return

    def part_fn(x):
        if len(x) == 1:
            return x[0]
        else:
            return term(rator, ctor(x))

    for p in partitions(rands, n, 1, part_fn=part_fn):
        yield ctor(p)


def assoc_flatteno(a, a_flat, no_ident=False, null_type=etuple):
    """Construct a goal that flattens/normalizes terms with associative operators.

    The normal/canonical form is left-associative, e.g.
        `(op, 1, 2, 3, 4) == (op, (op, (op, 1, 2), 3), 4)`

    Parameters
    ----------
    a: Var or Sequence
        The "input" term to flatten.
    a_flat: Var or Sequence
        The flattened result, or "output", term.
    no_ident: bool (optional)
        Whether or not to fail if no flattening occurs.
    """

    def assoc_flatteno_goal(S):
        nonlocal a, a_flat

        a_rf, a_flat_rf = reify((a, a_flat), S)

        if isinstance(a_rf, TermType) and (operator(a_rf),) in associative.facts:

            a_op = operator(a_rf)
            args_rf = arguments(a_rf)

            def op_pred(sub_op):
                return sub_op == a_op

            a_flat_rf = term(a_op, flatten_assoc_args(op_pred, args_rf))

            if a_flat_rf == a_rf and no_ident:
                return

            yield from eq(a_flat, a_flat_rf)(S)

        elif (
            isinstance(a_flat_rf, TermType)
            and (operator(a_flat_rf),) in associative.facts
        ):

            a_flat_op = operator(a_flat_rf)
            args_rf = arguments(a_flat_rf)
            assoc_args_iter = assoc_args(a_flat_op, args_rf)

            # TODO: There are much better ways to do this `no_ident` check
            # (e.g. the `n` argument of `assoc_args` should probably be made to
            # work for this)
            yield from lany(
                fail if no_ident and r is args_rf else applyo(a_flat_op, r, a_rf)
                for r in assoc_args_iter
            )(S)

        else:

            op = var()
            a_rands = var()
            a_rands_rands = var()
            a_flat_rands = var()
            a_flat_rands_rands = var()

            g = conde(
                [fail if no_ident else eq(a_rf, a_flat_rf)],
                [
                    associative(op),
                    applyo(op, a_rands, a_rf),
                    applyo(op, a_flat_rands, a_flat_rf),
                    # There must be at least two rands
                    conso(var(), a_rands_rands, a_rands),
                    conso(var(), var(), a_rands_rands),
                    conso(var(), a_flat_rands_rands, a_flat_rands),
                    conso(var(), var(), a_flat_rands_rands),
                    itero(
                        a_flat_rands, nullo_refs=(a_rands,), default_ConsNull=null_type
                    ),
                    Zzz(assoc_flatteno, a_rf, a_flat_rf, no_ident=no_ident),
                ],
            )

            yield from g(S)

    return assoc_flatteno_goal


def eq_assoc_args(
    op, a_args, b_args, n=None, inner_eq=eq, no_ident=False, null_type=etuple
):
    """Create a goal that applies associative unification to an operator and two sets of arguments.

    This is a non-relational utility goal.  It assumes that the op and at least
    one set of arguments are ground under the state in which it is evaluated.
    """
    u_args, v_args = var(), var()

    def eq_assoc_args_goal(S):
        nonlocal op, u_args, v_args, n

        (op_rf, u_args_rf, v_args_rf, n_rf) = reify((op, u_args, v_args, n), S)

        if isinstance(v_args_rf, Sequence):
            u_args_rf, v_args_rf = v_args_rf, u_args_rf

        if isinstance(u_args_rf, Sequence) and isinstance(v_args_rf, Sequence):
            # TODO: We just ignore `n` when both are sequences?

            if type(u_args_rf) != type(v_args_rf):
                return

            if no_ident and unify(u_args_rf, v_args_rf, S) is not False:
                return

            op_pred = partial(equal, op_rf)
            u_args_flat = type(u_args_rf)(flatten_assoc_args(op_pred, u_args_rf))
            v_args_flat = type(v_args_rf)(flatten_assoc_args(op_pred, v_args_rf))

            u_len, v_len = len(u_args_flat), len(v_args_flat)
            if u_len == v_len:
                g = inner_eq(u_args_flat, v_args_flat)
            else:
                if u_len < v_len:
                    sm_args, lg_args = u_args_flat, v_args_flat
                    grp_sizes = u_len
                else:
                    sm_args, lg_args = v_args_flat, u_args_flat
                    grp_sizes = v_len

                assoc_terms = assoc_args(
                    op_rf, lg_args, grp_sizes, ctor=type(u_args_rf)
                )

                g = conde([inner_eq(sm_args, a_args)] for a_args in assoc_terms)

            yield from g(S)

        elif isinstance(u_args_rf, Sequence):
            # TODO: We really need to know the arity (ranges) for the operator
            # in order to make good choices here.
            # For instance, does `(op, 1, 2) == (op, (op, 1, 2))` make sense?
            # If so, the lower-bound on this range should actually be `1`.
            if len(u_args_rf) == 1:
                if not no_ident and (n_rf == 1 or n_rf is None):
                    g = inner_eq(u_args_rf, v_args_rf)
                else:
                    return
            else:

                u_args_flat = list(flatten_assoc_args(partial(equal, op_rf), u_args_rf))

                g = conde(
                    [inner_eq(v_args_rf, v_ac_arg)]
                    for v_ac_arg in assoc_args(
                        op_rf, u_args_flat, n_rf, ctor=type(u_args_rf)
                    )
                    if not no_ident or v_ac_arg != u_args_rf
                )

            yield from g(S)

    return lall(
        ground_order((a_args, b_args), (u_args, v_args)),
        itero(u_args, nullo_refs=(v_args,), default_ConsNull=null_type),
        eq_assoc_args_goal,
    )


def eq_assoc(u, v, n=None, op_predicate=associative, null_type=etuple, no_ident=False):
    """Create a goal for associative unification of two terms.

    Warning: This goal walks the left-hand argument, `u`, so make that argument
    the most ground term; otherwise, it may iterate indefinitely when it should
    actually terminate.

    >>> from kanren import run, var, fact
    >>> from kanren.assoccomm import eq_assoc as eq

    >>> fact(commutative, 'add')    # declare that 'add' is commutative
    >>> fact(associative, 'add')    # declare that 'add' is associative

    >>> x = var()
    >>> run(0, x, eq(('add', 1, 2, 3), ('add', 1, x)))
    (('add', 2, 3),)
    """

    def assoc_args_unique(a, b, op, **kwargs):
        return eq_assoc_args(op, a, b, no_ident=True, null_type=null_type)

    return term_walko(op_predicate, assoc_args_unique, u, v, n=n, no_ident=no_ident)


def eq_comm(u, v, op_predicate=commutative, null_type=etuple, no_ident=False):
    """Create a goal for commutative equality.

    Warning: This goal walks the left-hand argument, `u`, so make that argument
    the most ground term; otherwise, it may iterate indefinitely when it should
    actually terminate.

    >>> from kanren import run, var, fact
    >>> from kanren.assoccomm import eq_comm as eq
    >>> from kanren.assoccomm import commutative, associative

    >>> fact(commutative, 'add')    # declare that 'add' is commutative
    >>> fact(associative, 'add')    # declare that 'add' is associative

    >>> x = var()
    >>> run(0, x, eq(('add', 1, 2, 3), ('add', 2, x, 1)))
    (3,)
    """

    def permuteo_unique(x, y, op, **kwargs):
        return permuteo(x, y, no_ident=True, default_ConsNull=null_type)

    return term_walko(op_predicate, permuteo_unique, u, v, no_ident=no_ident)


def eq_assoccomm(u, v, null_type=etuple):
    """Construct a goal for associative and commutative unification.

    Warning: This goal walks the left-hand argument, `u`, so make that argument
    the most ground term; otherwise, it may iterate indefinitely when it should
    actually terminate.

    >>> from kanren.assoccomm import eq_assoccomm as eq
    >>> from kanren.assoccomm import commutative, associative
    >>> from kanren import fact, run, var

    >>> fact(commutative, 'add')    # declare that 'add' is commutative
    >>> fact(associative, 'add')    # declare that 'add' is associative

    >>> x = var()
    >>> e1 = ('add', 1, 2, 3)
    >>> e2 = ('add', 1, x)
    >>> run(0, x, eq(e1, e2))
    (('add', 3, 2), ('add', 2, 3))
    """

    def eq_assoccomm_step(a, b, op):
        z = var()
        return lall(
            # Permute
            conde(
                [
                    commutative(op),
                    permuteo(a, z, no_ident=True, default_ConsNull=etuple),
                ],
                [eq(a, z)],
            ),
            # Generate associative combinations
            conde(
                [associative(op), eq_assoc_args(op, z, b, no_ident=True)], [eq(z, b)]
            ),
        )

    return term_walko(
        lambda x: succeed,
        eq_assoccomm_step,
        u,
        v,
        format_step=assoc_flatteno,
        no_ident=False,
    )
