"""Functions for associative and commutative unification.

This module provides goals for associative and commutative unification.  It
accomplishes this through naively trying all possibilities.  This was built to
be used in the computer algebra systems SymPy and Theano.

>>> from kanren import run, var, fact
>>> from kanren.assoccomm import eq_assoccomm as eq
>>> from kanren.assoccomm import commutative, associative

>>> # Define some dummy Ops
>>> add = 'add'
>>> mul = 'mul'

>>> # Declare that these ops are commutative using the facts system
>>> fact(commutative, mul)
>>> fact(commutative, add)
>>> fact(associative, mul)
>>> fact(associative, add)

>>> # Define some wild variables
>>> x, y = var('x'), var('y')

>>> # Two expressions to match
>>> pattern = (mul, (add, 1, x), y)                # (1 + x) * y
>>> expr    = (mul, 2, (add, 3, 1))                # 2 * (3 + 1)

>>> print(run(0, (x,y), eq(pattern, expr)))
((3, 2),)
"""
from collections.abc import Sequence
from functools import partial
from operator import eq as equal
from operator import length_hint

from cons.core import ConsPair, car, cdr
from etuples import etuple
from toolz import sliding_window
from unification import reify, unify, var

from .core import conde, eq, ground_order, lall, succeed
from .facts import Relation
from .goals import itero, permuteo
from .graph import term_walko
from .term import term

associative = Relation("associative")
commutative = Relation("commutative")


def flatten_assoc_args(op_predicate, items):
    for i in items:
        if isinstance(i, ConsPair) and op_predicate(car(i)):
            i_cdr = cdr(i)
            if length_hint(i_cdr) > 0:
                yield from flatten_assoc_args(op_predicate, i_cdr)
            else:
                yield i
        else:
            yield i


def assoc_args(rator, rands, n, ctor=None):
    """Produce all associative argument combinations of rator + rands in n-sized rand groupings.

    >>> from kanren.assoccomm import assoc_args
    >>> list(assoc_args('op', [1, 2, 3], 2))
    [[['op', 1, 2], 3], [1, ['op', 2, 3]]]
    """  # noqa: E501
    assert n > 0

    rands_l = list(rands)

    if ctor is None:
        ctor = type(rands)

    if n == len(rands_l):
        yield ctor(rands)
        return

    for i, new_rands in enumerate(sliding_window(n, rands_l)):
        prefix = rands_l[:i]
        new_term = term(rator, ctor(new_rands))
        suffix = rands_l[n + i :]
        res = ctor(prefix + [new_term] + suffix)
        yield res


def eq_assoc_args(
    op, a_args, b_args, n=None, inner_eq=eq, no_ident=False, null_type=etuple
):
    """Create a goal that applies associative unification to an operator and two sets of arguments.

    This is a non-relational utility goal.  It does assumes that the op and at
    least one set of arguments are ground under the state in which it is
    evaluated.
    """  # noqa: E501
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

            if len(u_args_flat) == len(v_args_flat):
                g = inner_eq(u_args_flat, v_args_flat)
            else:
                if len(u_args_flat) < len(v_args_flat):
                    sm_args, lg_args = u_args_flat, v_args_flat
                else:
                    sm_args, lg_args = v_args_flat, u_args_flat

                grp_sizes = len(lg_args) - len(sm_args) + 1
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

                if n_rf is not None:
                    arg_sizes = [n_rf]
                else:
                    arg_sizes = range(2, len(u_args_flat) + (not no_ident))

                v_ac_args = (
                    v_ac_arg
                    for n_i in arg_sizes
                    for v_ac_arg in assoc_args(
                        op_rf, u_args_flat, n_i, ctor=type(u_args_rf)
                    )
                    if not no_ident or v_ac_arg != u_args_rf
                )
                g = conde([inner_eq(v_args_rf, v_ac_arg)] for v_ac_arg in v_ac_args)

            yield from g(S)

    return lall(
        ground_order((a_args, b_args), (u_args, v_args)),
        itero(u_args, nullo_refs=(v_args,), default_ConsNull=null_type),
        eq_assoc_args_goal,
    )


def eq_assoc(u, v, n=None, op_predicate=associative, null_type=etuple):
    """Create a goal for associative unification of two terms.

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

    return term_walko(op_predicate, assoc_args_unique, u, v, n=n)


def eq_comm(u, v, op_predicate=commutative, null_type=etuple):
    """Create a goal for commutative equality.

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

    return term_walko(op_predicate, permuteo_unique, u, v)


def assoc_flatten(a, a_flat):
    def assoc_flatten_goal(S):
        nonlocal a, a_flat

        a_rf = reify(a, S)

        if isinstance(a_rf, Sequence) and (a_rf[0],) in associative.facts:

            def op_pred(sub_op):
                nonlocal S
                sub_op_rf = reify(sub_op, S)
                return sub_op_rf == a_rf[0]

            a_flat_rf = type(a_rf)(flatten_assoc_args(op_pred, a_rf))
        else:
            a_flat_rf = a_rf

        yield from eq(a_flat, a_flat_rf)(S)

    return assoc_flatten_goal


def eq_assoccomm(u, v, null_type=etuple):
    """Construct a goal for associative and commutative unification.

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
        format_step=assoc_flatten,
        no_ident=False,
    )
