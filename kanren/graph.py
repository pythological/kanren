from functools import partial

from unification import var, isvar
from unification import reify

from cons.core import ConsError

from etuples import apply, rands, rator

from .core import eq, conde, lall, goaleval
from .goals import conso, nullo


def applyo(o_rator, o_rands, obj):
    """Construct a goal that relates an object to the application of its (ope)rator to its (ope)rands.

    In other words, this is the relation `op(*args) == obj`.  It uses the
    `rator`, `rands`, and `apply` dispatch functions from `etuples`, so
    implement/override those to get the desired behavior.

    """

    def applyo_goal(S):
        nonlocal o_rator, o_rands, obj

        o_rator_rf, o_rands_rf, obj_rf = reify((o_rator, o_rands, obj), S)

        if not isvar(obj_rf):

            # We should be able to use this goal with *any* arguments, so
            # fail when the ground operations fail/err.
            try:
                obj_rator, obj_rands = rator(obj_rf), rands(obj_rf)
            except (ConsError, NotImplementedError):
                return

            # The object's rator + rands should be the same as the goal's
            yield from goaleval(
                lall(eq(o_rator_rf, obj_rator), eq(o_rands_rf, obj_rands))
            )(S)

        elif isvar(o_rands_rf) or isvar(o_rator_rf):
            # The object and at least one of the rand, rators is a logic
            # variable, so let's just assert a `cons` relationship between
            # them
            yield from goaleval(conso(o_rator_rf, o_rands_rf, obj_rf))(S)
        else:
            # The object is a logic variable, but the rator and rands aren't.
            # We assert that the object is the application of the rand and
            # rators.
            try:
                obj_applied = apply(o_rator_rf, o_rands_rf)
            except (ConsError, NotImplementedError):
                return
            yield from eq(obj_rf, obj_applied)(S)

    return applyo_goal


def map_anyo(relation, l_in, l_out, null_type=list):
    """Apply a relation to corresponding elements in two sequences and succeed if at least one pair succeeds.

    Empty `l_in` and/or `l_out` will fail--i.e. `relation` must succeed *at least once*.

    Parameters
    ----------
    null_type: optional
       An object that's a valid cdr for the collection type desired.  If
       `False` (i.e. the default value), the cdr will be inferred from the
       inputs, or defaults to an empty list.
    """

    def _map_anyo(relation, l_in, l_out, i_any):
        def map_anyo_goal(s):

            nonlocal relation, l_in, l_out, i_any, null_type

            l_in_rf, l_out_rf = reify((l_in, l_out), s)

            i_car, i_cdr = var(), var()
            o_car, o_cdr = var(), var()

            conde_branches = []

            if i_any or (isvar(l_in_rf) and isvar(l_out_rf)):
                # Consider terminating the sequences when we've had at least
                # one successful goal or when both sequences are logic variables.
                conde_branches.append(
                    [nullo(l_in_rf, l_out_rf, default_ConsNull=null_type)]
                )

            # Extract the CAR and CDR of each argument sequence; this is how we
            # iterate through elements of the two sequences.
            cons_parts_branch = [
                goaleval(conso(i_car, i_cdr, l_in_rf)),
                goaleval(conso(o_car, o_cdr, l_out_rf)),
            ]

            conde_branches.append(cons_parts_branch)

            conde_relation_branches = []

            relation_branch = [
                # This case tries the relation and continues on.
                relation(i_car, o_car),
                # In this conde clause, we can tell future calls to
                # `map_anyo` that we've had at least one successful
                # application of the relation (otherwise, this clause
                # would fail due to the above goal).
                _map_anyo(relation, i_cdr, o_cdr, True),
            ]

            conde_relation_branches.append(relation_branch)

            base_branch = [
                # This is the "base" case; it is used when, for example,
                # the given relation isn't satisfied.
                eq(i_car, o_car),
                _map_anyo(relation, i_cdr, o_cdr, i_any),
            ]

            conde_relation_branches.append(base_branch)

            cons_parts_branch.append(conde(*conde_relation_branches))

            g = conde(*conde_branches)

            yield from goaleval(g)(s)

        return map_anyo_goal

    return _map_anyo(relation, l_in, l_out, False)


def reduceo(relation, in_term, out_term):
    """Relate a term and the fixed-point of that term under a given relation.

    This includes the "identity" relation.
    """

    def reduceo_goal(s):

        nonlocal in_term, out_term, relation

        in_term_rf, out_term_rf = reify((in_term, out_term), s)

        # The result of reducing the input graph once
        term_rdcd = var()

        # Are we working "backward" and (potentially) "expanding" a graph
        # (e.g. when the relation is a reduction rule)?
        is_expanding = isvar(in_term_rf)

        # One application of the relation assigned to `term_rdcd`
        single_apply_g = relation(in_term_rf, term_rdcd)

        # Assign/equate (unify, really) the result of a single application to
        # the "output" term.
        single_res_g = eq(term_rdcd, out_term_rf)

        # Recurse into applications of the relation (well, produce a goal that
        # will do that)
        another_apply_g = reduceo(relation, term_rdcd, out_term_rf)

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

        g = goaleval(g)
        yield from g(s)

    return reduceo_goal


def walko(goal, graph_in, graph_out, rator_goal=None, null_type=False):
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
    """

    def walko_goal(s):

        nonlocal goal, rator_goal, graph_in, graph_out, null_type

        graph_in_rf, graph_out_rf = reify((graph_in, graph_out), s)

        rator_in, rands_in, rator_out, rands_out = var(), var(), var(), var()

        _walko = partial(walko, goal, rator_goal=rator_goal, null_type=null_type)

        g = conde(
            [goal(graph_in_rf, graph_out_rf),],
            [
                lall(
                    applyo(rator_in, rands_in, graph_in_rf),
                    applyo(rator_out, rands_out, graph_out_rf),
                    rator_goal(rator_in, rator_out),
                    map_anyo(_walko, rands_in, rands_out, null_type=null_type),
                )
                if rator_goal is not None
                else lall(
                    map_anyo(_walko, graph_in_rf, graph_out_rf, null_type=null_type)
                ),
            ],
        )

        yield from goaleval(g)(s)

    return walko_goal
