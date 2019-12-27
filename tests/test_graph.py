from operator import add, mul
from functools import partial
from math import log, exp

import pytest

from unification import var, unify

from kanren import run, eq, conde, lall
from kanren.constraints import isinstanceo

from etuples.core import etuple, ExpressionTuple
from kanren.graph import reduceo, seq_apply_anyo, graph_applyo


class OrderedFunction(object):
    def __init__(self, func):
        self.func = func

    def __call__(self, *args, **kwargs):
        return self.func(*args, **kwargs)

    @property
    def __name__(self):
        return self.func.__name__

    def __lt__(self, other):
        return self.__name__ < getattr(other, "__name__", str(other))

    def __gt__(self, other):
        return self.__name__ > getattr(other, "__name__", str(other))

    def __repr__(self):
        return self.__name__


add = OrderedFunction(add)
mul = OrderedFunction(mul)
log = OrderedFunction(log)
exp = OrderedFunction(exp)


ExpressionTuple.__lt__ = (
    lambda self, other: self < (other,)
    if isinstance(other, int)
    else tuple(self) < tuple(other)
)
ExpressionTuple.__gt__ = (
    lambda self, other: self > (other,)
    if isinstance(other, int)
    else tuple(self) > tuple(other)
)


def math_reduceo(in_expr, out_expr):
    """Create a relation for a couple math-based identities."""
    x_lv = var(prefix="x")

    return lall(
        conde(
            [eq(in_expr, etuple(add, x_lv, x_lv)), eq(out_expr, etuple(mul, 2, x_lv))],
            [eq(in_expr, etuple(log, etuple(exp, x_lv))), eq(out_expr, x_lv)],
        ),
        conde(
            [isinstanceo(in_expr, float)],
            [isinstanceo(in_expr, int)],
            [isinstanceo(in_expr, ExpressionTuple)],
            [isinstanceo(out_expr, float)],
            [isinstanceo(out_expr, int)],
            [isinstanceo(out_expr, ExpressionTuple)],
        ),
    )


def full_math_reduceo(a, b):
    """Produce all results for repeated applications of the math-based relation."""
    return (reduceo, math_reduceo, a, b)


def fixedp_graph_applyo(r, x, y):
    return reduceo(partial(graph_applyo, r, preprocess_graph=None), x, y)


def test_basics():
    x_lv = var()
    res = unify(
        etuple(log, etuple(exp, etuple(log, 1))), etuple(log, etuple(exp, x_lv))
    )
    assert res[x_lv] == etuple(log, 1)


def test_reduceo():
    q_lv = var()

    # Reduce/forward
    res = run(
        0, q_lv, full_math_reduceo(etuple(log, etuple(exp, etuple(log, 1))), q_lv)
    )
    assert len(res) == 1
    assert res[0] == etuple(log, 1)

    res = run(
        0,
        q_lv,
        full_math_reduceo(etuple(log, etuple(exp, etuple(log, etuple(exp, 1)))), q_lv),
    )
    assert res[0] == 1
    assert res[1] == etuple(log, etuple(exp, 1))

    # Expand/backward
    res = run(2, q_lv, full_math_reduceo(q_lv, 1))
    assert res[0] == etuple(log, etuple(exp, 1))
    assert res[1] == etuple(log, etuple(exp, etuple(log, etuple(exp, 1))))


def test_seq_apply_anyo_types():
    """Make sure that `applyo` preserves the types between its arguments."""
    q_lv = var()
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), [1], q_lv))
    assert res[0] == [1]
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), (1,), q_lv))
    assert res[0] == (1,)
    res = run(
        1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), etuple(1,), q_lv, skip_op=False)
    )
    assert res[0] == etuple(1,)
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), q_lv, (1,)))
    assert res[0] == (1,)
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), q_lv, [1]))
    assert res[0] == [1]
    res = run(
        1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), q_lv, etuple(1), skip_op=False)
    )
    assert res[0] == etuple(1)
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), [1, 2], [1, 2]))
    assert len(res) == 1
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), [1, 2], [1, 3]))
    assert len(res) == 0
    res = run(1, q_lv, seq_apply_anyo(lambda x, y: eq(x, y), [1, 2], (1, 2)))
    assert len(res) == 0
    res = run(
        0,
        q_lv,
        seq_apply_anyo(
            lambda x, y: eq(y, etuple(mul, 2, x)), etuple(add, 1, 2), q_lv, skip_op=True
        ),
    )
    assert len(res) == 3
    assert all(r[0] == add for r in res)


def test_seq_apply_anyo_misc():
    q_lv = var("q")

    assert len(run(0, q_lv, seq_apply_anyo(eq, [1, 2, 3], [1, 2, 3]))) == 1

    assert len(run(0, q_lv, seq_apply_anyo(eq, [1, 2, 3], [1, 3, 3]))) == 0

    def one_to_threeo(x, y):
        return conde([eq(x, 1), eq(y, 3)])

    res = run(0, q_lv, seq_apply_anyo(one_to_threeo, [1, 2, 4, 1, 4, 1, 1], q_lv))

    assert res[0] == [3, 2, 4, 3, 4, 3, 3]

    assert (
        len(
            run(4, q_lv, seq_apply_anyo(math_reduceo, [etuple(mul, 2, var("x"))], q_lv))
        )
        == 0
    )

    test_res = run(4, q_lv, seq_apply_anyo(math_reduceo, [etuple(add, 2, 2), 1], q_lv))
    assert test_res == ([etuple(mul, 2, 2), 1],)

    test_res = run(4, q_lv, seq_apply_anyo(math_reduceo, [1, etuple(add, 2, 2)], q_lv))
    assert test_res == ([1, etuple(mul, 2, 2)],)

    test_res = run(4, q_lv, seq_apply_anyo(math_reduceo, q_lv, var("z")))
    assert all(isinstance(r, list) for r in test_res)

    test_res = run(4, q_lv, seq_apply_anyo(math_reduceo, q_lv, var("z"), tuple()))
    assert all(isinstance(r, tuple) for r in test_res)


@pytest.mark.parametrize(
    "test_input, test_output",
    [
        ([], ()),
        ([1], ()),
        ([etuple(add, 1, 1),], ([etuple(mul, 2, 1)],)),
        ([1, etuple(add, 1, 1)], ([1, etuple(mul, 2, 1)],)),
        ([etuple(add, 1, 1), 1], ([etuple(mul, 2, 1), 1],)),
        (
            [etuple(mul, 2, 1), etuple(add, 1, 1), 1],
            ([etuple(mul, 2, 1), etuple(mul, 2, 1), 1],),
        ),
        (
            [etuple(add, 1, 1), etuple(log, etuple(exp, 5)),],
            (
                [etuple(mul, 2, 1), 5],
                [etuple(add, 1, 1), 5],
                [etuple(mul, 2, 1), etuple(log, etuple(exp, 5))],
            ),
        ),
    ],
)
def test_seq_apply_anyo(test_input, test_output):
    """Test `seq_apply_anyo` with fully ground terms (i.e. no logic variables)."""
    q_lv = var()
    test_res = run(0, q_lv, (seq_apply_anyo, full_math_reduceo, test_input, q_lv))

    assert len(test_res) == len(test_output)

    test_res = sorted(test_res)
    test_output = sorted(test_output)
    # Make sure the first result matches.
    # TODO: This is fairly implementation-specific (i.e. dependent on the order
    # in which `condeseq` returns results).
    if len(test_output) > 0:
        assert test_res[0] == test_output[0]

    # Make sure all the results match.
    # TODO: If we want to avoid fixing the output order, convert the lists to
    # tuples and add everything to a set, then compare.
    assert test_res == test_output


def test_seq_apply_anyo_reverse():
    """Test `seq_apply_anyo` in "reverse" (i.e. specify the reduced form and generate the un-reduced form)."""
    # Unbounded reverse
    q_lv = var()
    rev_input = [etuple(mul, 2, 1)]
    test_res = run(4, q_lv, (seq_apply_anyo, math_reduceo, q_lv, rev_input))
    assert test_res == (
        [etuple(add, 1, 1)],
        [etuple(log, etuple(exp, etuple(mul, 2, 1)))],
    )

    # Guided reverse
    test_res = run(
        4,
        q_lv,
        (seq_apply_anyo, math_reduceo, [etuple(add, q_lv, 1)], [etuple(mul, 2, 1)]),
    )

    assert test_res == (1,)


def test_graph_applyo_misc():
    q_lv = var("q")
    expr = etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1))
    assert len(run(0, q_lv, graph_applyo(eq, expr, expr, preprocess_graph=None))) == 1

    expr2 = etuple(add, etuple(mul, 2, 1), etuple(add, 2, 1))
    assert len(run(0, q_lv, graph_applyo(eq, expr, expr2, preprocess_graph=None))) == 0

    assert (
        len(run(0, q_lv, graph_applyo(eq, etuple(), etuple(), preprocess_graph=None)))
        == 1
    )

    def one_to_threeo(x, y):
        return conde([eq(x, 1), eq(y, 3)])

    res = run(
        0,
        q_lv,
        graph_applyo(
            one_to_threeo,
            [1, [1, 2, 4], 2, [[4, 1, 1]], 1],
            q_lv,
            preprocess_graph=None,
        ),
    )

    assert res[0] == [3, [3, 2, 4], 2, [[4, 3, 3]], 3]


@pytest.mark.parametrize(
    "test_input, test_output",
    [
        (1, ()),
        (etuple(add, 1, 1), (etuple(mul, 2, 1),)),
        (
            etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1)),
            (
                etuple(mul, 2, etuple(mul, 2, 1)),
                etuple(add, etuple(mul, 2, 1), etuple(mul, 2, 1)),
            ),
        ),
        (
            etuple(add, etuple(mul, etuple(log, etuple(exp, 2)), 1), etuple(add, 1, 1)),
            (
                etuple(mul, 2, etuple(mul, 2, 1)),
                etuple(add, etuple(mul, 2, 1), etuple(mul, 2, 1)),
                etuple(
                    add, etuple(mul, etuple(log, etuple(exp, 2)), 1), etuple(mul, 2, 1)
                ),
                etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1)),
            ),
        ),
    ],
)
def test_graph_applyo(test_input, test_output):
    """Test `graph_applyo` with fully ground terms (i.e. no logic variables)."""

    q_lv = var()
    test_res = run(
        len(test_output), q_lv, fixedp_graph_applyo(full_math_reduceo, test_input, q_lv)
    )

    assert len(test_res) == len(test_output)

    test_res = sorted(test_res)
    test_output = sorted(test_output)

    # Make sure the first result matches.
    if len(test_output) > 0:
        assert test_res[0] == test_output[0]

    # Make sure all the results match.
    assert set(test_res) == set(test_output)


def test_graph_applyo_reverse():
    """Test `graph_applyo` in "reverse" (i.e. specify the reduced form and generate the un-reduced form)."""
    q_lv = var("q")

    test_res = run(2, q_lv, fixedp_graph_applyo(math_reduceo, q_lv, 5))
    assert test_res == (
        etuple(log, etuple(exp, 5)),
        etuple(log, etuple(exp, etuple(log, etuple(exp, 5)))),
    )
    assert all(e.eval_obj == 5.0 for e in test_res)

    # Make sure we get some variety in the results
    test_res = run(2, q_lv, fixedp_graph_applyo(math_reduceo, q_lv, etuple(mul, 2, 5)))
    assert test_res == (
        # Expansion of the term's root
        etuple(add, 5, 5),
        # Expansion in the term's arguments
        # etuple(mul, etuple(log, etuple(exp, 2)), etuple(log, etuple(exp, 5))),
        # Two step expansion at the root
        etuple(log, etuple(exp, etuple(add, 5, 5))),
        # Expansion into a sub-term
        # etuple(mul, 2, etuple(log, etuple(exp, 5)))
    )
    assert all(e.eval_obj == 10.0 for e in test_res)

    r_lv = var("r")
    test_res = run(4, [q_lv, r_lv], fixedp_graph_applyo(math_reduceo, q_lv, r_lv))
    expect_res = (
        [etuple(add, 1, 1), etuple(mul, 2, 1)],
        [etuple(log, etuple(exp, etuple(add, 1, 1))), etuple(mul, 2, 1)],
        [etuple(), etuple()],
        [
            etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1)),
            etuple(mul, 2, etuple(mul, 2, 1)),
        ],
    )
    assert list(
        unify(a1, a2) and unify(b1, b2)
        for [a1, b1], [a2, b2] in zip(test_res, expect_res)
    )
