from functools import partial

from unification import var, isvar
from unification import reify

from etuples import etuple

from .core import Zzz, conde, eq, fail, lall, succeed
from .goals import conso, nullo
from .term import applyo


def mapo(*args, null_res=True, **kwargs):
    """Apply a relation to corresponding elements in two sequences and succeed if the relation succeeds for all sets of elements.

    See `map_anyo` for parameter descriptions.
    """
    return map_anyo(*args, null_res=null_res, _first=True, _any_succeed=None, **kwargs)


def map_anyo(
    relation,
    *args,
    null_type=list,
    null_res=False,
    _first=True,
    _any_succeed=False,
    **kwargs
):
    """Apply a relation to corresponding elements across sequences and succeed if at least one set of elements succeeds.

    Parameters
    ----------
    relation: Callable
       The goal to apply across elements (`car`s, specifically) of `args`.
    *args: Sequence
       Argument list containing terms that are walked and evaluated as
       `relation(car(a_1), car(a_2), ...)`.
    null_type: optional
       An object that's a valid cdr for the collection type desired.  If
       `False` (i.e. the default value), the cdr will be inferred from the
       inputs, or defaults to an empty list.
    null_res: bool
       Succeed on empty lists.
    _first: bool
       Indicate whether or not this is the first iteration in a call to this
       goal constructor (in contrast to a recursive call).
       This is not a user-level parameter.
    _any_succeed: bool or None
       Indicate whether or not an iteration has succeeded in a recursive call
       to this goal, or, if `None`, indicate that only the relation against the
       `cars` should be checked (i.e. no "any" functionality).
       This is not a user-level parameter.
    **kwargs: dict
       Keyword arguments to `relation`.
    """

    cars = tuple(var() for a in args)
    cdrs = tuple(var() for a in args)

    conde_branches = [
        [
            Zzz(relation, *cars, **kwargs),
            Zzz(
                map_anyo,
                relation,
                *cdrs,
                null_type=null_type,
                null_res=null_res,
                _first=False,
                _any_succeed=True if _any_succeed is not None else None,
                **kwargs
            ),
        ]
    ]

    if _any_succeed is not None:
        nullo_condition = _any_succeed or (_first and null_res)
        conde_branches.append(
            [eq(a_car, b_car) for a_car, b_car in zip(cars, cars[1:])]
            + [
                Zzz(
                    map_anyo,
                    relation,
                    *cdrs,
                    null_type=null_type,
                    null_res=null_res,
                    _first=False,
                    _any_succeed=_any_succeed,
                    **kwargs
                ),
            ]
        )
    else:
        nullo_condition = not _first or null_res

    return conde(
        [nullo(*args, default_ConsNull=null_type) if nullo_condition else fail],
        [conso(car, cdr, arg) for car, cdr, arg in zip(cars, cdrs, args)]
        + [conde(*conde_branches)],
    )


def vararg_success(*args):
    return succeed


def eq_length(u, v, default_ConsNull=list):
    """Construct a goal stating that two sequences are the same length and type."""

    return mapo(vararg_success, u, v, null_type=default_ConsNull)


def reduceo(relation, in_term, out_term, *args, **kwargs):
    """Relate a term and the fixed-point of that term under a given relation.

    This includes the "identity" relation.
    """

    def reduceo_goal(s):

        nonlocal in_term, out_term, relation, args, kwargs

        in_term_rf, out_term_rf = reify((in_term, out_term), s)

        # The result of reducing the input graph once
        term_rdcd = var()

        # Are we working "backward" and (potentially) "expanding" a graph
        # (e.g. when the relation is a reduction rule)?
        is_expanding = isvar(in_term_rf)

        # One application of the relation assigned to `term_rdcd`
        single_apply_g = relation(in_term_rf, term_rdcd, *args, **kwargs)

        # Assign/equate (unify, really) the result of a single application to
        # the "output" term.
        single_res_g = eq(term_rdcd, out_term_rf)

        # Recurse into applications of the relation (well, produce a goal that
        # will do that)
        another_apply_g = reduceo(relation, term_rdcd, out_term_rf, *args, **kwargs)

        # We want the fixed-point value to show up in the stream output
        # *first*, but that requires some checks.
        if is_expanding:
            # When an un-reduced term is a logic variable (e.g. we're
            # "expanding"), we can't go depth first.
            # We need to draw the association between (i.e. unify) the reduced
            # and expanded terms ASAP, in order to produce finite
            # expanded graphs first and yield results.
            #
            # In other words, there's no fixed-point to produce in this
            # situation.  Instead, for example, we have to produce an infinite
            # stream of terms that have `out_term_rf` as a fixed point.
            # g = conde([single_res_g, single_apply_g],
            #           [another_apply_g, single_apply_g])
            g = lall(conde([single_res_g], [another_apply_g]), single_apply_g)
        else:
            # Run the recursion step first, so that we get the fixed-point as
            # the first result
            g = lall(single_apply_g, conde([another_apply_g], [single_res_g]))

        yield from g(s)

    return reduceo_goal


def walko(
    goal,
    graph_in,
    graph_out,
    rator_goal=None,
    null_type=etuple,
    map_rel=partial(map_anyo, null_res=True),
):
    """Apply a binary relation between all nodes in two graphs.

    When `rator_goal` is used, the graphs are treated as term graphs, and the
    multi-functions `rator`, `rands`, and `apply` are used to walk the graphs.
    Otherwise, the graphs must be iterable according to `map_anyo`.

    Parameters
    ----------
    goal: callable
        A goal that is applied to all terms in the graph.
    graph_in: object
        The graph for which the left-hand side of a binary relation holds.
    graph_out: object
        The graph for which the right-hand side of a binary relation holds.
    rator_goal: callable (default None)
        A goal that is applied to the rators of a graph.  When specified,
        `goal` is only applied to rands and it must succeed along with the
        rator goal in order to descend into sub-terms.
    null_type: type
        The collection type used when it is not fully determined by the graph
        arguments.
    map_rel: callable
        The map relation used to apply `goal` to a sub-graph.
    """

    rator_in, rands_in, rator_out, rands_out = var(), var(), var(), var()

    _walko = partial(
        walko, goal, rator_goal=rator_goal, null_type=null_type, map_rel=map_rel
    )

    return conde(
        [Zzz(goal, graph_in, graph_out),],
        [
            applyo(rator_in, rands_in, graph_in),
            applyo(rator_out, rands_out, graph_out),
            Zzz(rator_goal, rator_in, rator_out),
            Zzz(map_rel, _walko, rands_in, rands_out, null_type=null_type),
        ]
        if rator_goal is not None
        else [Zzz(map_rel, _walko, graph_in, graph_out, null_type=null_type)],
    )


def term_walko(
    rator_goal,
    rands_goal,
    a,
    b,
    null_type=etuple,
    no_ident=False,
    format_step=None,
    **kwargs
):
    """Construct a goal for walking a term graph.

    This implementation is somewhat specific to the needs of `eq_comm` and
    `eq_assoc`, but it could be transferred to `kanren.graph`.

    XXX: Make sure `rator_goal` will succeed for unground logic variables;
    otherwise, this will diverge.
    XXX: `rands_goal` should not be contain `eq`, i.e. `rands_goal(x, x)`
    should always fail!
    """

    def single_step(u, v):
        u_rator, u_rands = var(), var()
        v_rands = var()

        return lall(
            applyo(u_rator, u_rands, u),
            applyo(u_rator, v_rands, v),
            rator_goal(u_rator),
            # These make sure that there are at least two rands, which
            # makes sense for commutativity and associativity, at least.
            conso(var(), var(), u_rands),
            conso(var(), var(), v_rands),
            Zzz(rands_goal, u_rands, v_rands, u_rator, **kwargs),
        )

    def term_walko_step(u, v):
        nonlocal rator_goal, rands_goal, null_type
        z, w = var(), var()

        return lall(
            format_step(u, w) if format_step is not None else eq(u, w),
            conde(
                [
                    # Apply, then walk or return
                    single_step(w, v),
                ],
                [
                    # Walk, then apply or return
                    map_anyo(term_walko_step, w, z, null_type=null_type),
                    conde([eq(z, v)], [single_step(z, v)]),
                ],
            ),
        )

    return lall(
        term_walko_step(a, b)
        if no_ident
        else conde([term_walko_step(a, b)], [eq(a, b)]),
    )
