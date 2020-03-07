from functools import partial

from unification import var, isvar
from unification import reify

from etuples import etuple

from .core import Zzz, conde, eq, fail, lall, succeed, ground_order_seqs
from .goals import conso, nullo
from .term import applyo


def mapo(*args, null_res=True, **kwargs):
    """Apply a goal to corresponding elements in two sequences and succeed if the goal succeeds for all sets of elements.

    See `map_anyo` for parameter descriptions.
    """
    return map_anyo(*args, null_res=null_res, _first=True, _any_succeed=None, **kwargs)


def map_anyo(
    goal,
    *args,
    null_type=list,
    null_res=False,
    use_ground_ordering=True,
    _first=True,
    _any_succeed=False,
    **kwargs,
):
    """Apply a goal to corresponding elements across sequences and succeed if at least one set of elements succeeds.

    Parameters
    ----------
    goal: Callable
       The goal to apply across elements (`car`s, specifically) of `args`.
    *args: Sequence
       Argument list containing terms that are walked and evaluated as
       `goal(car(a_1), car(a_2), ...)`.
    null_type: optional
       An object that's a valid cdr for the collection type desired.  If
       `False` (i.e. the default value), the cdr will be inferred from the
       inputs, or defaults to an empty list.
    null_res: bool
       Succeed on empty lists.
    use_ground_ordering: bool
        Order arguments by their "groundedness" before recursing.
    _first: bool
       Indicate whether or not this is the first iteration in a call to this
       goal constructor (in contrast to a recursive call).
       This is not a user-level parameter.
    _any_succeed: bool or None
       Indicate whether or not an iteration has succeeded in a recursive call
       to this goal, or, if `None`, indicate that only the goal against the
       `cars` should be checked (i.e. no "any" functionality).
       This is not a user-level parameter.
    **kwargs: dict
       Keyword arguments to `goal`.
    """

    cars = tuple(var() for a in args)
    cdrs = tuple(var() for a in args)

    conde_branches = [
        [
            Zzz(goal, *cars, **kwargs),
            Zzz(
                map_anyo,
                goal,
                *cdrs,
                null_type=null_type,
                null_res=null_res,
                _first=False,
                _any_succeed=True if _any_succeed is not None else None,
                **kwargs,
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
                    goal,
                    *cdrs,
                    null_type=null_type,
                    null_res=null_res,
                    _first=False,
                    _any_succeed=_any_succeed,
                    **kwargs,
                ),
            ]
        )
    else:
        nullo_condition = not _first or null_res

    if use_ground_ordering:
        args_ord = tuple(var() for t in args)
        ground_order_goal = ground_order_seqs(args, args_ord)
    else:
        args_ord = args
        ground_order_goal = succeed

    return conde(
        [nullo(*args, default_ConsNull=null_type) if nullo_condition else fail],
        [ground_order_goal]
        + [conso(car, cdr, arg) for car, cdr, arg in zip(cars, cdrs, args_ord)]
        + [conde(*conde_branches)],
    )


def vararg_success(*args):
    return succeed


def eq_length(u, v, default_ConsNull=list):
    """Construct a goal stating that two sequences are the same length and type."""

    return mapo(vararg_success, u, v, null_type=default_ConsNull)


def reduceo(goal, in_term, out_term, *args, **kwargs):
    """Construct a goal that yields the fixed-point of another goal.

    It simply tries to order the implicit `conde` recursion branches so that they
    produce the fixed-point value first.  All goals that follow are the reductions
    leading up to the fixed-point.

    FYI: The results will include `eq(in_term, out_term)`.
    """

    def reduceo_goal(s):

        nonlocal in_term, out_term, goal, args, kwargs

        in_term_rf, out_term_rf = reify((in_term, out_term), s)

        # The result of reducing the input graph once
        term_rdcd = var()

        # Are we working "backward" and (potentially) "expanding" a graph
        # (e.g. when the goal is a reduction rule)?
        is_expanding = isvar(in_term_rf)

        # One application of the goal assigned to `term_rdcd`
        single_apply_g = goal(in_term_rf, term_rdcd, *args, **kwargs)

        # Assign/equate (unify, really) the result of a single application to
        # the "output" term.
        single_res_g = eq(term_rdcd, out_term_rf)

        # Recurse into applications of the goal (well, produce a goal that
        # will do that)
        another_apply_g = reduceo(goal, term_rdcd, out_term_rf, *args, **kwargs)

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
    *terms,
    pre_process_fn=None,
    null_type=etuple,
    map_rel=partial(map_anyo, null_res=True),
):
    """Apply a goal between all nodes in a set of terms.

    Parameters
    ----------
    goal: callable
        A goal that is applied to all terms and their sub-terms.
    *terms: Sequence of objects
        The terms to be walked.
    pre_process_fn: callable (default None)
        A goal with a signature of the form `(old_terms, new_terms)`, where
        each argument is a list of corresponding terms.
        This goal can be used to transform terms before walking them.
    null_type: type
        The collection type used when it is not fully determined by the `terms`
        arguments.
    map_rel: callable
        The map goal used to apply `goal` to corresponding sub-terms.
    """

    if pre_process_fn is not None:
        terms_pp = tuple(var() for t in terms)
        pre_process_goal = pre_process_fn(*(terms + terms_pp))
    else:
        terms_pp = terms
        pre_process_goal = succeed

    _walko = partial(
        walko,
        goal,
        pre_process_fn=pre_process_fn,
        null_type=null_type,
        map_rel=map_rel,
    )

    return lall(
        pre_process_goal,
        conde(
            [Zzz(goal, *terms_pp)],
            [Zzz(map_rel, _walko, *terms_pp, null_type=null_type)],
        ),
    )


def term_walko(
    rator_goal,
    rands_goal,
    a,
    b,
    null_type=etuple,
    no_ident=False,
    format_step=None,
    **kwargs,
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
