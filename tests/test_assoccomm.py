import pytest

from itertools import chain

from etuples.core import etuple

from cons import cons

from unification import reify, var, isvar, unify

from kanren.core import run
from kanren.facts import fact
from kanren.assoccomm import (
    associative,
    commutative,
    eq_assoc_args,
    eq_comm,
    eq_assoc,
    eq_assoccomm,
    assoc_args,
    flatten_assoc_args,
    partitions,
    assoc_flatteno,
)

from tests.utils import Add


def results(g, s=None):
    if s is None:
        s = dict()
    return tuple(g(s))


def test_eq_comm():
    commutative.facts.clear()
    commutative.index.clear()

    comm_op = "comm_op"

    fact(commutative, comm_op)

    x, y, z = var(), var(), var()

    assert run(0, True, eq_comm(1, 1)) == (True,)
    assert run(0, True, eq_comm((comm_op, 1, 2, 3), (comm_op, 1, 2, 3))) == (True,)

    assert run(0, True, eq_comm((comm_op, 3, 2, 1), (comm_op, 1, 2, 3))) == (True,)
    assert run(0, y, eq_comm((comm_op, 1, 2, 3), (comm_op, 3, y, 1))) == (2,)
    assert run(0, (x, y), eq_comm((comm_op, 1, 2, 3), (comm_op, x, y, 1))) == (
        (2, 3),
        (3, 2),
    )
    assert run(0, (x, y), eq_comm((comm_op, 2, 3, 1), (comm_op, 1, x, y))) == (
        (2, 3),
        (3, 2),
    )

    assert not run(
        0, True, eq_comm(("op", 3, 2, 1), ("op", 1, 2, 3))
    )  # not commutative
    assert not run(0, True, eq_comm((3, comm_op, 2, 1), (comm_op, 1, 2, 3)))
    assert not run(0, True, eq_comm((comm_op, 1, 2, 1), (comm_op, 1, 2, 3)))
    assert not run(0, True, eq_comm(("op", 1, 2, 3), (comm_op, 1, 2, 3)))

    # Make sure it can unify single elements
    assert (3,) == run(0, x, eq_comm((comm_op, 1, 2, 3), (comm_op, 2, x, 1)))

    # `eq_comm` should propagate through
    assert (3,) == run(
        0, x, eq_comm(("div", 1, (comm_op, 1, 2, 3)), ("div", 1, (comm_op, 2, x, 1)))
    )
    # Now it should not
    assert () == run(
        0, x, eq_comm(("div", 1, ("div", 1, 2, 3)), ("div", 1, ("div", 2, x, 1)))
    )

    expected_res = {(1, 2, 3), (2, 1, 3), (3, 1, 2), (1, 3, 2), (2, 3, 1), (3, 2, 1)}
    assert expected_res == set(
        run(0, (x, y, z), eq_comm((comm_op, 1, 2, 3), (comm_op, x, y, z)))
    )
    # assert expected_res == set(
    #     run(0, (x, y, z), eq_comm((comm_op, x, y, z), (comm_op, 1, 2, 3)))
    # )
    assert expected_res == set(
        run(
            0,
            (x, y, z),
            eq_comm(("div", 1, (comm_op, 1, 2, 3)), ("div", 1, (comm_op, x, y, z))),
        )
    )

    e1 = (comm_op, 2, (comm_op, 3, 1))
    e2 = (comm_op, (comm_op, 1, x), y)
    assert run(0, (x, y), eq_comm(e1, e2)) == ((3, 2),)

    e1 = ((comm_op, 3, 1),)
    e2 = ((comm_op, 1, x),)
    assert run(0, x, eq_comm(e1, e2)) == (3,)

    e1 = (2, (comm_op, 3, 1))
    e2 = (y, (comm_op, 1, x))
    assert run(0, (x, y), eq_comm(e1, e2)) == ((3, 2),)


def test_eq_comm_all_variations():
    commutative.facts.clear()
    commutative.index.clear()

    comm_op = "comm_op"

    fact(commutative, comm_op)

    expected_res = {
        (comm_op, 1, (comm_op, 2, (comm_op, 3, 4))),
        (comm_op, 1, (comm_op, 2, (comm_op, 4, 3))),
        (comm_op, 1, (comm_op, (comm_op, 3, 4), 2)),
        (comm_op, 1, (comm_op, (comm_op, 4, 3), 2)),
        (comm_op, (comm_op, 2, (comm_op, 3, 4)), 1),
        (comm_op, (comm_op, 2, (comm_op, 4, 3)), 1),
        (comm_op, (comm_op, (comm_op, 3, 4), 2), 1),
        (comm_op, (comm_op, (comm_op, 4, 3), 2), 1),
    }

    x = var()
    res = run(0, x, eq_comm((comm_op, 1, (comm_op, 2, (comm_op, 3, 4))), x))
    assert sorted(res, key=str) == sorted(expected_res, key=str)


def test_eq_comm_unground():
    commutative.facts.clear()
    commutative.index.clear()

    comm_op = "comm_op"

    fact(commutative, comm_op)

    x, y, z = var(), var(), var()
    # Test for variable args
    res = run(4, (x, y), eq_comm(x, y))
    exp_res_form = (
        (etuple(comm_op, x, y), etuple(comm_op, y, x)),
        (x, y),
        (etuple(etuple(comm_op, x, y)), etuple(etuple(comm_op, y, x))),
        (etuple(comm_op, x, y, z), etuple(comm_op, x, z, y)),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False
        assert all(isvar(i) for i in reify((x, y, z), s))


@pytest.mark.xfail(reason="`applyo`/`buildo` needs to be a constraint.", strict=True)
def test_eq_comm_object():
    x = var()

    fact(commutative, Add)
    fact(associative, Add)

    assert run(0, x, eq_comm(Add(1, 2, 3), Add(3, 1, x))) == (2,)
    assert set(run(0, x, eq_comm(Add(1, 2), x))) == set((Add(1, 2), Add(2, 1)))
    assert set(run(0, x, eq_assoccomm(Add(1, 2, 3), Add(1, x)))) == set(
        (Add(2, 3), Add(3, 2))
    )


def test_flatten_assoc_args():
    op = "add"

    def op_pred(x):
        return x == op

    assert list(flatten_assoc_args(op_pred, [op, 1, 2, 3, 4])) == [op, 1, 2, 3, 4]
    assert list(flatten_assoc_args(op_pred, [op, 1, 2, [op]])) == [op, 1, 2, [op]]
    assert list(flatten_assoc_args(op_pred, [[op, 1, 2, [op]]])) == [1, 2, [op]]

    res = list(
        flatten_assoc_args(
            op_pred,
            [[1, 2, op], 3, [op, 4, [op, [op]]], [op, 5], 6, op, 7],
            shallow=False,
        )
    )
    exp_res = [[1, 2, op], 3, 4, [op], 5, 6, op, 7]
    assert res == exp_res

    exa_col = (1, 2, ("b", 3, ("a", 4, 5)), ("c", 6, 7), ("a", ("a", 8, 9), 10))
    assert list(flatten_assoc_args(lambda x: x == "a", exa_col, shallow=False)) == [
        1,
        2,
        ("b", 3, ("a", 4, 5)),
        ("c", 6, 7),
        8,
        9,
        10,
    ]

    assert list(flatten_assoc_args(lambda x: x == "a", exa_col, shallow=True)) == [
        1,
        2,
        ("b", 3, ("a", 4, 5)),
        ("c", 6, 7),
        ("a", 8, 9),
        10,
    ]


def test_partitions():

    assert list(partitions(("a",), 2, 2)) == []
    assert list(partitions(("a", "b"), 2, 2)) == []
    assert list(partitions(("a", "b"), 2, 1)) == [(("a",), ("b",))]
    assert list(partitions(("a", "b"), 2, 1, part_fn=lambda x: ("op",) + x)) == [
        (("op", "a"), ("op", "b"))
    ]

    exa_col = tuple("abcdefg")

    expected_res = [
        (("a", "b"), ("c", "d", "e", "f", "g")),
        (("a", "b", "c"), ("d", "e", "f", "g")),
        (("a", "b", "c", "d"), ("e", "f", "g")),
        (("a", "b", "c", "d", "e"), ("f", "g")),
    ]

    assert list(partitions(exa_col, 2, 2)) == expected_res

    expected_res = [
        (("a", "b"), ("c", "d"), ("e", "f", "g")),
        (("a", "b"), ("c", "d", "e"), ("f", "g")),
        (("a", "b", "c"), ("d", "e"), ("f", "g")),
    ]

    assert list(partitions(exa_col, 3, 2)) == expected_res

    expected_res = sorted(
        chain.from_iterable(
            [partitions(exa_col, i, 2) for i in range(2, len(exa_col) + 1)]
        )
    )
    assert sorted(partitions(exa_col, None, 2)) == expected_res

    res = list(
        partitions(
            tuple(range(1, 5)),
            None,
            1,
            part_fn=lambda x: x[0] if len(x) == 1 else ("op",) + x,
        )
    )
    assert res == [
        (1, ("op", 2, 3, 4)),
        (1, 2, ("op", 3, 4)),
        (1, 2, 3, 4),
        (1, ("op", 2, 3), 4),
        (("op", 1, 2), ("op", 3, 4)),
        (("op", 1, 2), 3, 4),
        (("op", 1, 2, 3), 4),
    ]

    res = list(
        partitions(
            tuple(range(1, 5)),
            2,
            1,
            part_fn=lambda x: x[0] if len(x) == 1 else ("op",) + x,
        )
    )
    assert res == [
        (1, ("op", 2, 3, 4)),
        (("op", 1, 2), ("op", 3, 4)),
        (("op", 1, 2, 3), 4),
    ]


def test_assoc_args():

    res = list(assoc_args("op", tuple(range(1, 5)), None))
    assert res == [
        (1, ("op", 2, 3, 4)),
        (1, 2, ("op", 3, 4)),
        (1, 2, 3, 4),
        (1, ("op", 2, 3), 4),
        (("op", 1, 2), ("op", 3, 4)),
        (("op", 1, 2), 3, 4),
        (("op", 1, 2, 3), 4),
    ]

    res = list(assoc_args("op", tuple(range(1, 5)), None, ctor=list))
    assert res == [
        [1, ["op", 2, 3, 4]],
        [1, 2, ["op", 3, 4]],
        [1, 2, 3, 4],
        [1, ["op", 2, 3], 4],
        [["op", 1, 2], ["op", 3, 4]],
        [["op", 1, 2], 3, 4],
        [["op", 1, 2, 3], 4],
    ]

    res = list(assoc_args("op", tuple(range(1, 5)), 2))
    assert res == [
        (1, ("op", 2, 3, 4)),
        (("op", 1, 2), ("op", 3, 4)),
        (("op", 1, 2, 3), 4),
    ]

    res = list(assoc_args("op", (1, 2), 1))
    assert res == [(1, 2)]

    res = list(assoc_args("op", (1, 2, 3), 4))
    assert res == [(1, 2, 3)]

    res = list(assoc_args("op", (1, 2, 3), 3))
    assert res == [(1, 2, 3)]

    res = list(assoc_args("op", [1, 2, 3], 3, ctor=tuple))
    assert res == [(1, 2, 3)]


def test_eq_assoc_args():

    assoc_op = "assoc_op"

    fact(associative, assoc_op)

    assert not run(0, True, eq_assoc_args(assoc_op, (1,), [1], n=None))
    assert run(0, True, eq_assoc_args(assoc_op, (1,), (1,), n=None)) == (True,)
    assert run(0, True, eq_assoc_args(assoc_op, (1, 1), (1, 1))) == (True,)
    assert run(0, True, eq_assoc_args(assoc_op, (1, 2, 3), (1, (assoc_op, 2, 3)))) == (
        True,
    )
    assert run(0, True, eq_assoc_args(assoc_op, (1, (assoc_op, 2, 3)), (1, 2, 3))) == (
        True,
    )
    assert run(
        0, True, eq_assoc_args(assoc_op, (1, (assoc_op, 2, 3), 4), (1, 2, 3, 4))
    ) == (True,)
    assert not run(
        0, True, eq_assoc_args(assoc_op, (1, 2, 3), (1, (assoc_op, 2, 3), 4))
    )

    x, y = var(), var()

    assert run(0, True, eq_assoc_args(assoc_op, (x,), (x,), n=None)) == (True,)
    assert run(0, x, eq_assoc_args(assoc_op, x, (y,), n=None)) == ((y,),)
    assert run(0, x, eq_assoc_args(assoc_op, (y,), x, n=None)) == ((y,),)

    assert run(0, x, eq_assoc_args(assoc_op, (1, x, 4), (1, 2, 3, 4))) == (
        (assoc_op, 2, 3),
    )
    assert run(0, x, eq_assoc_args(assoc_op, (1, 2, 3, 4), (1, x, 4))) == (
        (assoc_op, 2, 3),
    )
    assert run(0, x, eq_assoc_args(assoc_op, [1, x, 4], [1, 2, 3, 4])) == (
        [assoc_op, 2, 3],
    )
    assert run(0, True, eq_assoc_args(assoc_op, (1, 1), ("other_op", 1, 1))) == ()

    assert run(0, x, eq_assoc_args(assoc_op, (1, 2, 3), x, n=2)) == (
        (1, (assoc_op, 2, 3)),
        ((assoc_op, 1, 2), 3),
    )
    assert run(0, x, eq_assoc_args(assoc_op, x, (1, 2, 3), n=2)) == (
        (1, (assoc_op, 2, 3)),
        ((assoc_op, 1, 2), 3),
    )

    assert run(0, x, eq_assoc_args(assoc_op, (1, 2, 3), x)) == (
        (1, (assoc_op, 2, 3)),
        (1, 2, 3),
        ((assoc_op, 1, 2), 3),
    )

    assert () not in run(0, x, eq_assoc_args(assoc_op, (), x, no_ident=True))
    assert (1,) not in run(0, x, eq_assoc_args(assoc_op, (1,), x, no_ident=True))
    assert (1, 2, 3) not in run(
        0, x, eq_assoc_args(assoc_op, (1, 2, 3), x, no_ident=True)
    )

    assert (
        run(
            0,
            True,
            eq_assoc_args(
                assoc_op, (1, (assoc_op, 2, 3)), (1, (assoc_op, 2, 3)), no_ident=True,
            ),
        )
        == ()
    )

    assert run(
        0,
        True,
        eq_assoc_args(
            assoc_op, (1, (assoc_op, 2, 3)), ((assoc_op, 1, 2), 3), no_ident=True,
        ),
    ) == (True,)


def test_eq_assoc():

    associative.index.clear()
    associative.facts.clear()

    assoc_op = "assoc_op"

    fact(associative, assoc_op)

    assert run(0, True, eq_assoc(1, 1)) == (True,)
    assert run(0, True, eq_assoc((assoc_op, 1, 2, 3), (assoc_op, 1, 2, 3))) == (True,)
    assert not run(0, True, eq_assoc((assoc_op, 3, 2, 1), (assoc_op, 1, 2, 3)))
    assert run(
        0, True, eq_assoc((assoc_op, (assoc_op, 1, 2), 3), (assoc_op, 1, 2, 3))
    ) == (True,)
    assert run(
        0, True, eq_assoc((assoc_op, 1, 2, 3), (assoc_op, (assoc_op, 1, 2), 3))
    ) == (True,)
    o = "op"
    assert not run(0, True, eq_assoc((o, 1, 2, 3), (o, (o, 1, 2), 3)))

    x, y = var(), var()

    res = run(0, x, eq_assoc((assoc_op, 1, 2, 3), x, n=2))
    assert res == (
        (assoc_op, 1, (assoc_op, 2, 3)),
        (assoc_op, 1, 2, 3),
        (assoc_op, (assoc_op, 1, 2), 3),
    )

    # Make sure it works with `cons`
    res = run(0, (x, y), eq_assoc((assoc_op, 1, 2, 3), cons(x, y)))
    assert sorted(res, key=str) == sorted(
        [
            (assoc_op, (1, (assoc_op, 2, 3))),
            (assoc_op, (1, 2, 3)),
            (assoc_op, ((assoc_op, 1, 2), 3)),
        ],
        key=str,
    )

    # XXX: Don't use a predicate that can never succeed, e.g.
    # associative_2 = Relation("associative_2")
    # run(1, (x, y), eq_assoc(cons(x, y), (x, z), op_predicate=associative_2))

    # Nested expressions should work now
    expr1 = (assoc_op, (assoc_op, 1, 2), 3, 4, 5, 6)
    expr2 = (assoc_op, 1, 2, (assoc_op, x, 5, 6))
    assert run(0, x, eq_assoc(expr1, expr2, n=2)) == ((assoc_op, 3, 4),)


@pytest.mark.xfail(strict=False)
def test_eq_assoc_cons():
    associative.index.clear()
    associative.facts.clear()

    assoc_op = "assoc_op"

    fact(associative, assoc_op)

    x, y, z = var(), var(), var()

    res = run(1, (x, y), eq_assoc(cons(x, y), (x, z, 2, 3)))
    assert res == ((assoc_op, (z, (assoc_op, 2, 3))),)


@pytest.mark.xfail(strict=False)
def test_eq_assoc_all_variations():

    associative.index.clear()
    associative.facts.clear()

    assoc_op = "assoc_op"

    fact(associative, assoc_op)

    x = var()
    # Normalized, our results are left-associative, i.e.
    # (assoc_op, (assoc_op, (assoc_op, 1, 2), 3), 4) == (assoc_op, 1, 2, 3, 4)
    expected_res = {
        (assoc_op, (assoc_op, (assoc_op, 1, 2), 3), 4),  # Missing
        (assoc_op, (assoc_op, 1, (assoc_op, 2, 3)), 4),  # Missing
        (assoc_op, (assoc_op, 1, 2), (assoc_op, 3, 4)),
        (assoc_op, (assoc_op, 1, 2), 3, 4),
        (assoc_op, (assoc_op, 1, 2, 3), 4),
        (assoc_op, 1, (assoc_op, (assoc_op, 2, 3), 4)),  # Missing
        (assoc_op, 1, (assoc_op, 2, (assoc_op, 3, 4))),  # Missing
        (assoc_op, 1, (assoc_op, 2, 3), 4),
        (assoc_op, 1, (assoc_op, 2, 3, 4)),
        (assoc_op, 1, 2, (assoc_op, 3, 4)),
        (assoc_op, 1, 2, 3, 4),
    }
    res = run(0, x, eq_assoc((assoc_op, 1, 2, 3, 4), x))
    assert sorted(res, key=str) == sorted(expected_res, key=str)


def test_eq_assoc_unground():

    associative.index.clear()
    associative.facts.clear()

    assoc_op = "assoc_op"

    fact(associative, assoc_op)

    x, y = var(), var()
    xx, yy, zz = var(), var(), var()

    # Check results when both arguments are variables
    res = run(3, (x, y), eq_assoc(x, y))
    exp_res_form = (
        (etuple(assoc_op, xx, yy, zz), etuple(assoc_op, xx, etuple(assoc_op, yy, zz))),
        (xx, yy),
        (
            etuple(etuple(assoc_op, xx, yy, zz)),
            etuple(etuple(assoc_op, xx, etuple(assoc_op, yy, zz))),
        ),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False, (a, b)
        assert all(isvar(i) for i in reify((xx, yy, zz), s))


def test_assoc_flatteno():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    add = "add"
    mul = "mul"

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)
    fact(associative, Add)

    assert run(
        0,
        True,
        assoc_flatteno((mul, 1, (add, 2, 3), (mul, 4, 5)), (mul, 1, (add, 2, 3), 4, 5)),
    ) == (True,)

    x = var()
    assert run(0, x, assoc_flatteno((mul, 1, (add, 2, 3), (mul, 4, 5)), x)) == (
        (mul, 1, (add, 2, 3), 4, 5),
    )

    assert run(
        0,
        True,
        assoc_flatteno(
            ("op", 1, (add, 2, 3), (mul, 4, 5)), ("op", 1, (add, 2, 3), (mul, 4, 5))
        ),
    ) == (True,)

    assert run(0, x, assoc_flatteno(("op", 1, (add, 2, 3), (mul, 4, 5)), x)) == (
        ("op", 1, (add, 2, 3), (mul, 4, 5)),
    )

    assert run(
        0, True, assoc_flatteno((add, 1, (add, 2, 3), (mul, 4, 5)), x, no_ident=True)
    ) == (True,)

    assert (
        run(
            0,
            True,
            assoc_flatteno((add, 1, (mul, 2, 3), (mul, 4, 5)), x, no_ident=True),
        )
        == ()
    )

    assert run(0, True, assoc_flatteno((add, 1, 2, 3), x)) == (True,)
    assert run(0, True, assoc_flatteno(Add(1, 2, 3), x)) == (True,)
    assert run(0, True, assoc_flatteno((add, 1, 2, 3), x, no_ident=True)) == ()

    res = run(0, x, assoc_flatteno(x, (add, 1, 2, 3), no_ident=True))
    assert sorted(res, key=str) == sorted(
        [(add,) + r for r in assoc_args(add, (1, 2, 3)) if r != (add, 1, 2, 3)], key=str
    )

    res = run(0, x, assoc_flatteno(x, (add, 1, 2, 3), no_ident=True))
    assert sorted(res, key=str) == sorted(
        [(add,) + r for r in assoc_args(add, (1, 2, 3)) if r != (add, 1, 2, 3)], key=str
    )


def test_assoc_flatteno_unground():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    add = "add"
    mul = "mul"

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)

    x, y = var(), var()

    xx, yy, zz = var(), var(), var()
    op_lv = var()
    exp_res_form = (
        (xx, yy),
        (etuple(op_lv, xx, yy), etuple(op_lv, xx, yy)),
        (etuple(op_lv, xx, yy), etuple(op_lv, xx, yy)),
        (etuple(op_lv, xx, etuple(op_lv, yy, zz)), etuple(op_lv, xx, yy, zz)),
    )

    res = run(4, (x, y), assoc_flatteno(x, y))

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False, (a, b)
        assert op_lv not in s or (s[op_lv],) in associative.facts
        assert all(isvar(i) for i in reify((xx, yy, zz), s))

    ww = var()
    exp_res_form = (
        (etuple(op_lv, xx, etuple(op_lv, yy, zz)), etuple(op_lv, xx, yy, zz)),
        (etuple(op_lv, xx, etuple(op_lv, yy, zz)), etuple(op_lv, xx, yy, zz)),
        (etuple(op_lv, xx, etuple(op_lv, yy, zz, ww)), etuple(op_lv, xx, yy, zz, ww)),
    )
    res = run(3, (x, y), assoc_flatteno(x, y, no_ident=True))

    for a, b in zip(res, exp_res_form):
        assert a[0] != a[1]
        s = unify(a, b)
        assert s is not False, (a, b)
        assert op_lv not in s or (s[op_lv],) in associative.facts
        assert all(isvar(i) for i in reify((xx, yy, zz, ww), s))


def test_eq_assoccomm():

    associative.index.clear()
    associative.facts.clear()
    commutative.index.clear()
    commutative.facts.clear()

    ac = "commassoc_op"

    fact(commutative, ac)
    fact(associative, ac)

    x, y = var(), var()

    assert run(0, True, eq_assoccomm(1, 1)) == (True,)
    assert run(0, True, eq_assoccomm((1,), (1,))) == (True,)
    # assert run(0, True, eq_assoccomm(x, (1,))) == (True,)
    assert run(0, True, eq_assoccomm((1,), x)) == (True,)

    # Assoc only
    assert run(0, True, eq_assoccomm((ac, 1, (ac, 2, 3)), (ac, (ac, 1, 2), 3))) == (
        True,
    )
    # Commute only
    assert run(0, True, eq_assoccomm((ac, 1, (ac, 2, 3)), (ac, (ac, 3, 2), 1))) == (
        True,
    )
    # Both
    assert run(0, True, eq_assoccomm((ac, 1, (ac, 3, 2)), (ac, (ac, 1, 2), 3))) == (
        True,
    )

    assert run(0, (x, y), eq_assoccomm((ac, 2, (ac, 3, 1)), (ac, (ac, 1, x), y))) == (
        (2, 3),
        (3, 2),
    )
    # assert run(0, (x, y), eq_assoccomm((ac, (ac, 1, x), y), (ac, 2, (ac, 3, 1)))) == (
    #     (2, 3),
    #     (3, 2),
    # )

    assert run(0, True, eq_assoccomm((ac, (ac, 1, 2), 3), (ac, 1, 2, 3))) == (True,)
    assert run(0, True, eq_assoccomm((ac, 3, (ac, 1, 2)), (ac, 1, 2, 3))) == (True,)
    assert run(0, True, eq_assoccomm((ac, 1, 1), ("other_op", 1, 1))) == ()

    assert run(0, x, eq_assoccomm((ac, 3, (ac, 1, 2)), (ac, 1, x, 3))) == (2,)


def test_eq_assoccomm_all_variations():

    associative.index.clear()
    associative.facts.clear()
    commutative.index.clear()
    commutative.facts.clear()

    ac = "commassoc_op"

    fact(commutative, ac)
    fact(associative, ac)

    x = var()

    # TODO: Use four arguments to see real associative variation.
    exp_res = set(
        (
            (ac, 1, 3, 2),
            (ac, 1, 2, 3),
            (ac, 2, 1, 3),
            (ac, 2, 3, 1),
            (ac, 3, 1, 2),
            (ac, 3, 2, 1),
            (ac, 1, (ac, 2, 3)),
            (ac, 1, (ac, 3, 2)),
            (ac, 2, (ac, 1, 3)),
            (ac, 2, (ac, 3, 1)),
            (ac, 3, (ac, 1, 2)),
            (ac, 3, (ac, 2, 1)),
            (ac, (ac, 2, 3), 1),
            (ac, (ac, 3, 2), 1),
            (ac, (ac, 1, 3), 2),
            (ac, (ac, 3, 1), 2),
            (ac, (ac, 1, 2), 3),
            (ac, (ac, 2, 1), 3),
        )
    )
    assert set(run(0, x, eq_assoccomm((ac, 1, (ac, 2, 3)), x))) == exp_res
    assert set(run(0, x, eq_assoccomm((ac, 1, 3, 2), x))) == exp_res
    assert set(run(0, x, eq_assoccomm((ac, 2, (ac, 3, 1)), x))) == exp_res


def test_eq_assoccomm_unground():

    associative.index.clear()
    associative.facts.clear()
    commutative.index.clear()
    commutative.facts.clear()

    ac = "commassoc_op"

    fact(commutative, ac)
    fact(associative, ac)

    x, y = var(), var()

    # Both arguments unground
    op_lv = var()
    z = var()
    res = run(4, (x, y), eq_assoccomm(x, y))
    exp_res_form = (
        (etuple(op_lv, x, y), etuple(op_lv, y, x)),
        (y, y),
        (etuple(op_lv, x, y), etuple(op_lv, y, x),),
        (etuple(op_lv, x, etuple(op_lv, y, z)), etuple(op_lv, x, etuple(op_lv, z, y))),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False, (a, b)
        assert (
            op_lv not in s
            or (s[op_lv],) in associative.facts
            or (s[op_lv],) in commutative.facts
        )
        assert all(isvar(i) for i in reify((x, y, z), s))


def test_eq_assoccomm_algebra():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    add = "add"
    mul = "mul"

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)

    x, y = var(), var()

    pattern = (mul, 2, (add, 3, 1))  # 2 * (3 + 1)
    expr = (mul, (add, 1, x), y)  # (1 + x) * y

    assert run(0, (x, y), eq_assoccomm(pattern, expr)) == ((3, 2),)


def test_eq_assoccomm_objects():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    fact(commutative, Add)
    fact(associative, Add)

    x = var()

    assert run(0, True, eq_assoccomm(Add(1, 2, 3), Add(3, 1, 2))) == (True,)
    # FYI: If `Node` is made `unifiable_with_term` (along with `term`,
    # `operator`, and `arguments` implementations), you'll get duplicate
    # results in the following test (i.e. `(3, 3)`).
    assert run(0, x, eq_assoccomm(Add(1, 2, 3), Add(1, 2, x))) == (3,)
    assert run(0, x, eq_assoccomm(Add(1, 2, 3), Add(x, 2, 1))) == (3,)


@pytest.mark.xfail(strict=False)
@pytest.mark.timeout(5)
def test_eq_assoccomm_scaling():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    add = "add"
    mul = "mul"

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)

    import random

    from tests.utils import generate_term

    random.seed(2343243)

    test_graph = generate_term((add, mul), range(4), 5)

    # Make a low-depth term inequal (e.g. inequal at base):
    # Change the root operator
    test_graph_2 = list(test_graph)
    test_graph_2[0] = add if test_graph_2[0] == mul else mul

    assert test_graph != test_graph_2
    assert test_graph[1:] == test_graph_2[1:]

    assert run(0, True, eq_assoccomm(test_graph, test_graph_2)) == ()

    # TODO: Make a high-depth term inequal
