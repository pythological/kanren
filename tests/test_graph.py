from functools import partial
from math import exp, log
from numbers import Real
from operator import add, mul

import pytest
import toolz
from cons import cons
from etuples.core import ExpressionTuple, etuple
from unification import isvar, reify, unify, var

from kanren import conde, eq, lall, run
from kanren.constraints import isinstanceo
from kanren.graph import eq_length, map_anyo, mapo, reduceo, walko


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


def single_math_reduceo(expanded_term, reduced_term):
    """Construct a goal for some simple math reductions."""
    x_lv = var()
    return lall(
        isinstanceo(x_lv, Real),
        isinstanceo(x_lv, ExpressionTuple),
        conde(
            [
                eq(expanded_term, etuple(add, x_lv, x_lv)),
                eq(reduced_term, etuple(mul, 2, x_lv)),
            ],
            [eq(expanded_term, etuple(log, etuple(exp, x_lv))), eq(reduced_term, x_lv)],
        ),
    )


math_reduceo = partial(reduceo, single_math_reduceo)

term_walko = partial(
    walko,
    rator_goal=eq,
    null_type=ExpressionTuple,
    map_rel=partial(map_anyo, null_res=False),
)


def test_basics():
    x_lv = var()
    res = unify(
        etuple(log, etuple(exp, etuple(log, 1))), etuple(log, etuple(exp, x_lv))
    )
    assert res[x_lv] == etuple(log, 1)


def test_reduceo():
    q_lv = var()

    # Reduce/forward
    res = run(0, q_lv, math_reduceo(etuple(log, etuple(exp, etuple(log, 1))), q_lv))
    assert len(res) == 1
    assert res[0] == etuple(log, 1)

    res = run(
        0,
        q_lv,
        math_reduceo(etuple(log, etuple(exp, etuple(log, etuple(exp, 1)))), q_lv),
    )
    assert res[0] == 1
    assert res[1] == etuple(log, etuple(exp, 1))

    # Expand/backward
    res = run(3, q_lv, math_reduceo(q_lv, 1))
    assert res[0] == etuple(log, etuple(exp, 1))
    assert res[1] == etuple(log, etuple(exp, etuple(log, etuple(exp, 1))))


def test_mapo():
    q_lv = var()

    def blah(x, y):
        return conde([eq(x, 1), eq(y, "a")], [eq(x, 3), eq(y, "b")])

    assert run(0, q_lv, mapo(blah, [], q_lv)) == ([],)
    assert run(0, q_lv, mapo(blah, [1, 2, 3], q_lv)) == ()
    assert run(0, q_lv, mapo(blah, [1, 1, 3], q_lv)) == (["a", "a", "b"],)
    assert run(0, q_lv, mapo(blah, q_lv, ["a", "a", "b"])) == ([1, 1, 3],)

    exp_res = (
        [[], []],
        [[1], ["a"]],
        [[3], ["b"]],
        [[1, 1], ["a", "a"]],
        [[3, 1], ["b", "a"]],
    )

    a_lv = var()
    res = run(5, [q_lv, a_lv], mapo(blah, q_lv, a_lv))
    assert res == exp_res


def test_eq_length():
    q_lv = var()

    res = run(0, q_lv, eq_length([1, 2, 3], q_lv))
    assert len(res) == 1 and len(res[0]) == 3 and all(isvar(q) for q in res[0])

    res = run(0, q_lv, eq_length(q_lv, [1, 2, 3]))
    assert len(res) == 1 and len(res[0]) == 3 and all(isvar(q) for q in res[0])

    res = run(0, q_lv, eq_length(cons(1, q_lv), [1, 2, 3]))
    assert len(res) == 1 and len(res[0]) == 2 and all(isvar(q) for q in res[0])

    v_lv = var()
    res = run(3, (q_lv, v_lv), eq_length(q_lv, v_lv, default_ConsNull=tuple))
    assert len(res) == 3 and all(
        isinstance(a, tuple)
        and len(a) == len(b)
        and (len(a) == 0 or a != b)
        and all(isvar(r) for r in a)
        for a, b in res
    )


def test_map_anyo_types():
    """Make sure that `map_anyo` preserves the types between its arguments."""
    q_lv = var()
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), [1], q_lv))
    assert res[0] == [1]
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), (1,), q_lv))
    assert res[0] == (1,)
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), q_lv, (1,)))
    assert res[0] == (1,)
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), q_lv, [1]))
    assert res[0] == [1]
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), [1, 2], [1, 2]))
    assert len(res) == 1
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), [1, 2], [1, 3]))
    assert len(res) == 0
    res = run(1, q_lv, map_anyo(lambda x, y: eq(x, y), [1, 2], (1, 2)))
    assert len(res) == 0


def test_map_anyo_misc():
    q_lv = var("q")

    res = run(0, q_lv, map_anyo(eq, [1, 2, 3], [1, 2, 3]))
    # TODO: Remove duplicate results
    assert len(res) == 7
    res = run(0, q_lv, map_anyo(eq, [1, 2, 3], [1, 3, 3]))
    assert len(res) == 0

    def one_to_threeo(x, y):
        return conde([eq(x, 1), eq(y, 3)])

    res = run(0, q_lv, map_anyo(one_to_threeo, [1, 2, 4, 1, 4, 1, 1], q_lv))

    assert res[0] == [3, 2, 4, 3, 4, 3, 3]

    assert (
        len(run(4, q_lv, map_anyo(math_reduceo, [etuple(mul, 2, var("x"))], q_lv))) == 0
    )

    test_res = run(4, q_lv, map_anyo(math_reduceo, [etuple(add, 2, 2), 1], q_lv))
    assert test_res == ([etuple(mul, 2, 2), 1],)

    test_res = run(4, q_lv, map_anyo(math_reduceo, [1, etuple(add, 2, 2)], q_lv))
    assert test_res == ([1, etuple(mul, 2, 2)],)

    test_res = run(4, q_lv, map_anyo(math_reduceo, q_lv, var("z")))
    assert all(isinstance(r, list) for r in test_res)

    test_res = run(4, q_lv, map_anyo(math_reduceo, q_lv, var("z"), tuple))
    assert all(isinstance(r, tuple) for r in test_res)

    x, y, z = var(), var(), var()

    def test_bin(a, b):
        return conde([eq(a, 1), eq(b, 2)])

    res = run(10, (x, y), map_anyo(test_bin, x, y, null_type=tuple))
    exp_res_form = (
        ((1,), (2,)),
        ((x, 1), (x, 2)),
        ((1, 1), (2, 2)),
        ((x, y, 1), (x, y, 2)),
        ((1, x), (2, x)),
        ((x, 1, 1), (x, 2, 2)),
        ((1, 1, 1), (2, 2, 2)),
        ((x, y, z, 1), (x, y, z, 2)),
        ((1, x, 1), (2, x, 2)),
        ((x, 1, y), (x, 2, y)),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False
        assert all(isvar(i) for i in reify((x, y, z), s))


@pytest.mark.parametrize(
    "test_input, test_output",
    [
        ([], ()),
        ([1], ()),
        (
            [
                etuple(add, 1, 1),
            ],
            ([etuple(mul, 2, 1)],),
        ),
        ([1, etuple(add, 1, 1)], ([1, etuple(mul, 2, 1)],)),
        ([etuple(add, 1, 1), 1], ([etuple(mul, 2, 1), 1],)),
        (
            [etuple(mul, 2, 1), etuple(add, 1, 1), 1],
            ([etuple(mul, 2, 1), etuple(mul, 2, 1), 1],),
        ),
        (
            [
                etuple(add, 1, 1),
                etuple(log, etuple(exp, 5)),
            ],
            (
                [etuple(mul, 2, 1), 5],
                [etuple(add, 1, 1), 5],
                [etuple(mul, 2, 1), etuple(log, etuple(exp, 5))],
            ),
        ),
    ],
)
def test_map_anyo(test_input, test_output):
    """Test `map_anyo` with fully ground terms (i.e. no logic variables)."""
    q_lv = var()
    test_res = run(
        0,
        q_lv,
        map_anyo(math_reduceo, test_input, q_lv),
    )

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


def test_map_anyo_reverse():
    """Test `map_anyo` in "reverse" (i.e. specify the reduced form and generate the un-reduced form)."""  # noqa: E501
    # Unbounded reverse
    q_lv = var()
    rev_input = [etuple(mul, 2, 1)]
    test_res = run(4, q_lv, map_anyo(math_reduceo, q_lv, rev_input))
    assert test_res == (
        [etuple(add, 1, 1)],
        [etuple(log, etuple(exp, etuple(add, 1, 1)))],
        # [etuple(log, etuple(exp, etuple(mul, 2, 1)))],
        [etuple(log, etuple(exp, etuple(log, etuple(exp, etuple(add, 1, 1)))))],
        # [etuple(log, etuple(exp, etuple(log, etuple(exp, etuple(mul, 2, 1)))))],
        [
            etuple(
                log,
                etuple(
                    exp,
                    etuple(
                        log, etuple(exp, etuple(log, etuple(exp, etuple(add, 1, 1))))
                    ),
                ),
            )
        ],
    )

    # Guided reverse
    test_res = run(
        4,
        q_lv,
        map_anyo(math_reduceo, [etuple(add, q_lv, 1)], [etuple(mul, 2, 1)]),
    )

    assert test_res == (1,)


def test_walko_misc():
    q_lv = var(prefix="q")

    expr = etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1))
    res = run(0, q_lv, walko(eq, expr, expr))
    # TODO: Remove duplicates
    assert len(res) == 162

    expr2 = etuple(add, etuple(mul, 2, 1), etuple(add, 2, 1))
    res = run(0, q_lv, walko(eq, expr, expr2))
    assert len(res) == 0

    def one_to_threeo(x, y):
        return conde([eq(x, 1), eq(y, 3)])

    res = run(
        1,
        q_lv,
        walko(
            one_to_threeo,
            [1, [1, 2, 4], 2, [[4, 1, 1]], 1],
            q_lv,
        ),
    )
    assert res == ([3, [3, 2, 4], 2, [[4, 3, 3]], 3],)

    assert run(2, q_lv, walko(eq, q_lv, q_lv, null_type=ExpressionTuple)) == (
        q_lv,
        etuple(),
    )

    res = run(
        1,
        q_lv,
        walko(
            one_to_threeo,
            etuple(
                add,
                1,
                etuple(mul, etuple(add, 1, 2), 1),
                etuple(add, etuple(add, 1, 2), 2),
            ),
            q_lv,
            # Only descend into `add` terms
            rator_goal=lambda x, y: lall(eq(x, add), eq(y, add)),
        ),
    )

    assert res == (
        etuple(
            add, 3, etuple(mul, etuple(add, 1, 2), 1), etuple(add, etuple(add, 3, 2), 2)
        ),
    )


@pytest.mark.parametrize(
    "test_input, test_output",
    [
        (1, ()),
        (etuple(add, 1, 1), (etuple(mul, 2, 1),)),
        (
            # (2 * 1) + (1 + 1)
            etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1)),
            (
                # 2 * (2 * 1)
                etuple(mul, 2, etuple(mul, 2, 1)),
                # (2 * 1) + (2 * 1)
                etuple(add, etuple(mul, 2, 1), etuple(mul, 2, 1)),
            ),
        ),
        (
            # (log(exp(2)) * 1) + (1 + 1)
            etuple(add, etuple(mul, etuple(log, etuple(exp, 2)), 1), etuple(add, 1, 1)),
            (
                # 2 * (2 * 1)
                etuple(mul, 2, etuple(mul, 2, 1)),
                # (2 * 1) + (2 * 1)
                etuple(add, etuple(mul, 2, 1), etuple(mul, 2, 1)),
                # (log(exp(2)) * 1) + (2 * 1)
                etuple(
                    add, etuple(mul, etuple(log, etuple(exp, 2)), 1), etuple(mul, 2, 1)
                ),
                etuple(add, etuple(mul, 2, 1), etuple(add, 1, 1)),
            ),
        ),
    ],
)
def test_walko(test_input, test_output):
    """Test `walko` with fully ground terms (i.e. no logic variables)."""

    q_lv = var()
    term_walko_fp = partial(reduceo, partial(term_walko, single_math_reduceo))
    test_res = run(
        len(test_output),
        q_lv,
        term_walko_fp(test_input, q_lv),
        results_filter=toolz.unique,
    )

    assert len(test_res) == len(test_output)

    test_res = sorted(test_res)
    test_output = sorted(test_output)

    # Make sure the first result matches.
    if len(test_output) > 0:
        assert test_res[0] == test_output[0]

    # Make sure all the results match.
    assert set(test_res) == set(test_output)


def test_walko_reverse():
    """Test `walko` in "reverse" (i.e. specify the reduced form and generate the un-reduced form)."""  # noqa: E501
    q_lv = var("q")

    test_res = run(2, q_lv, term_walko(math_reduceo, q_lv, 5))
    assert test_res == (
        etuple(log, etuple(exp, 5)),
        etuple(log, etuple(exp, etuple(log, etuple(exp, 5)))),
    )
    assert all(e.eval_obj == 5.0 for e in test_res)

    # Make sure we get some variety in the results
    test_res = run(2, q_lv, term_walko(math_reduceo, q_lv, etuple(mul, 2, 5)))
    assert test_res == (
        # Expansion of the term's root
        etuple(add, 5, 5),
        # Expansion in the term's arguments
        etuple(mul, etuple(log, etuple(exp, 2)), etuple(log, etuple(exp, 5))),
        # Two step expansion at the root
        # etuple(log, etuple(exp, etuple(add, 5, 5))),
        # Expansion into a sub-term
        # etuple(mul, 2, etuple(log, etuple(exp, 5)))
    )
    assert all(e.eval_obj == 10.0 for e in test_res)

    r_lv = var("r")
    test_res = run(4, [q_lv, r_lv], term_walko(math_reduceo, q_lv, r_lv))
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
