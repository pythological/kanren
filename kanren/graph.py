from functools import partial
from operator import length_hint

from unification import var, isvar
from unification import reify

from kanren import eq
from kanren.core import goaleval
from kanren.goals import conso, fail

from cons.core import ConsPair, ConsNull
from etuples.core import ExpressionTuple
from etuples.dispatch import etuplize

from .core import conde, lall


def seq_apply_anyo(relation, l_in, l_out, null_type=False, skip_op=True):
    """Apply a relation to at least one pair of corresponding elements in two sequences.

    Parameters
    ----------
    null_type: optional
       An object that's a valid cdr for the collection type desired.  If
       `False` (i.e. the default value), the cdr will be inferred from the
       inputs, or defaults to an empty list.
    skip_op: boolean (optional)
       When both inputs are `etuple`s and this value is `True`, the relation
       will not be applied to the operators (i.e. the cars) of the inputs.
    """

    # This is a customized (based on the initial call arguments) goal
    # constructor
    def _seq_apply_anyo(relation, l_in, l_out, i_any, null_type, skip_cars=False):
        def seq_apply_anyo_sub_goal(s):

            nonlocal i_any, null_type

            l_in_rf, l_out_rf = reify((l_in, l_out), s)

            i_car, i_cdr = var(), var()
            o_car, o_cdr = var(), var()

            conde_branches = []

            if i_any or (isvar(l_in_rf) and isvar(l_out_rf)):
                # Consider terminating the sequences when we've had at least
                # one successful goal or when both sequences are logic variables.
                conde_branches.append([eq(l_in_rf, null_type), eq(l_in_rf, l_out_rf)])

            # Extract the CAR and CDR of each argument sequence; this is how we
            # iterate through elements of the two sequences.
            cons_parts_branch = [
                goaleval(conso(i_car, i_cdr, l_in_rf)),
                goaleval(conso(o_car, o_cdr, l_out_rf)),
            ]

            conde_branches.append(cons_parts_branch)

            conde_relation_branches = []

            relation_branch = None

            if not skip_cars:
                relation_branch = [
                    # This case tries the relation continues on.
                    relation(i_car, o_car),
                    # In this conde clause, we can tell future calls to
                    # seq_apply_anyo that we've had at least one successful
                    # application of the relation (otherwise, this clause
                    # would fail due to the above goal).
                    _seq_apply_anyo(relation, i_cdr, o_cdr, True, null_type),
                ]

                conde_relation_branches.append(relation_branch)

            base_branch = [
                # This is the "base" case; it is used when, for example,
                # the given relation isn't satisfied.
                eq(i_car, o_car),
                _seq_apply_anyo(relation, i_cdr, o_cdr, i_any, null_type),
            ]

            conde_relation_branches.append(base_branch)

            cons_parts_branch.append(conde(*conde_relation_branches))

            g = conde(*conde_branches)
            g = goaleval(g)

            yield from g(s)

        return seq_apply_anyo_sub_goal

    def seq_apply_anyo_init_goal(s):

        nonlocal null_type, skip_op

        # We need the `cons` types to match in the end, which involves
        # using the same `cons`-null (i.e. terminating `cdr`).
        if null_type is False:
            l_out_, l_in_ = reify((l_out, l_in), s)

            out_null_type = False
            if isinstance(l_out_, (ConsPair, ConsNull)):
                out_null_type = type(l_out_)()

            in_null_type = False
            if isinstance(l_in_, (ConsPair, ConsNull)):
                in_null_type = type(l_in_)()

                if out_null_type is not False and not type(in_null_type) == type(
                    out_null_type
                ):
                    yield from fail(s)
                    return

            null_type = (
                out_null_type
                if out_null_type is not False
                else in_null_type
                if in_null_type is not False
                else []
            )

        g = _seq_apply_anyo(
            relation,
            l_in,
            l_out,
            False,
            null_type,
            skip_cars=isinstance(null_type, ExpressionTuple) and skip_op,
        )
        g = goaleval(g)

        yield from g(s)

    return seq_apply_anyo_init_goal


def reduceo(relation, in_term, out_term):
    """Relate a term and the fixed-point of that term under a given relation.

    This includes the "identity" relation.
    """

    def reduceo_goal(s):

        nonlocal in_term, out_term

        in_term_rf, out_term_rf = reify((in_term, out_term), s)

        # The result of reducing the input graph once
        term_rdcd = var()

        # Are we working "backward" and (potentially) "expanding" a graph
        # (e.g. when the relation is a reduction rule)?
        is_expanding = isvar(in_term_rf)

        # One application of the relation assigned to `term_rdcd`
        single_apply_g = (relation, in_term, term_rdcd)

        # Assign/equate (unify, really) the result of a single application to
        # the "output" term.
        single_res_g = eq(term_rdcd, out_term)

        # Recurse into applications of the relation (well, produce a goal that
        # will do that)
        another_apply_g = reduceo(relation, term_rdcd, out_term)

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
            # stream of terms that have `out_term` as a fixed point.
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


def graph_applyo(
    relation,
    in_graph,
    out_graph,
    preprocess_graph=partial(etuplize, shallow=True, return_bad_args=True),
):
    """Apply a relation to a graph and its subgraphs.

    Parameters
    ----------
    relation: callable
      A relation to apply on a graph and its subgraphs.
    in_graph: object
      The graph for which the left-hand side of a binary relation holds.
    out_graph: object
      The graph for which the right-hand side of a binary relation holds.
    preprocess_graph: callable (optional)
      A unary function that produces an iterable upon which `seq_apply_anyo`
      can be applied in order to traverse a graph's subgraphs.  The default
      function converts the graph to expression-tuple form.
    """

    if preprocess_graph in (False, None):

        def preprocess_graph(x):
            return x

    def graph_applyo_goal(s):

        nonlocal in_graph, out_graph

        in_graph_rf, out_graph_rf = reify((in_graph, out_graph), s)

        _gapply = partial(graph_applyo, relation, preprocess_graph=preprocess_graph)

        graph_reduce_gl = (relation, in_graph_rf, out_graph_rf)

        # We need to get the sub-graphs/children of the input graph/node
        if not isvar(in_graph_rf):
            in_subgraphs = preprocess_graph(in_graph_rf)
            in_subgraphs = None if length_hint(in_subgraphs, 0) == 0 else in_subgraphs
        else:
            in_subgraphs = in_graph_rf

        if not isvar(out_graph_rf):
            out_subgraphs = preprocess_graph(out_graph_rf)
            out_subgraphs = (
                None if length_hint(out_subgraphs, 0) == 0 else out_subgraphs
            )
        else:
            out_subgraphs = out_graph_rf

        conde_args = ([graph_reduce_gl],)

        # This goal reduces sub-graphs/children of the graph.
        if in_subgraphs is not None and out_subgraphs is not None:
            # We will only include it when there actually are children, or when
            # we're dealing with a logic variable (e.g. and "generating"
            # children).
            subgraphs_reduce_gl = seq_apply_anyo(_gapply, in_subgraphs, out_subgraphs)

            conde_args += ([subgraphs_reduce_gl],)

        g = conde(*conde_args)

        g = goaleval(g)
        yield from g(s)

    return graph_applyo_goal
