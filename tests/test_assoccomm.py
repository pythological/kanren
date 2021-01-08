from collections.abc import Sequence

import pytest
from cons import cons
from etuples.core import etuple
from unification import isvar, reify, unify, var

from kanren.assoccomm import (
    assoc_args,
    assoc_flatten,
    associative,
    commutative,
    eq_assoc,
    eq_assoc_args,
    eq_assoccomm,
    eq_comm,
    flatten_assoc_args,
)
from kanren.core import run
from kanren.facts import fact
from kanren.term import arguments, operator, term


class Node(object):
    def __init__(self, op, args):
        self.op = op
        self.args = args

    def __eq__(self, other):
        return (
            type(self) == type(other)
            and self.op == other.op
            and self.args == other.args
        )

    def __hash__(self):
        return hash((type(self), self.op, self.args))

    def __str__(self):
        return "%s(%s)" % (self.op.name, ", ".join(map(str, self.args)))

    __repr__ = __str__


class Operator(object):
    def __init__(self, name):
        self.name = name


Add = Operator("add")
Mul = Operator("mul")


def add(*args):
    return Node(Add, args)


def mul(*args):
    return Node(Mul, args)


@term.register(Operator, Sequence)
def term_Operator(op, args):
    return Node(op, args)


@arguments.register(Node)
def arguments_Node(n):
    return n.args


@operator.register(Node)
def operator_Node(n):
    return n.op


def results(g, s=None):
    if s is None:
        s = dict()
    return tuple(g(s))


def test_eq_comm():
    x, y, z = var(), var(), var()

    commutative.facts.clear()
    commutative.index.clear()

    comm_op = "comm_op"

    fact(commutative, comm_op)

    assert run(0, True, eq_comm(1, 1)) == (True,)
    assert run(0, True, eq_comm((comm_op, 1, 2, 3), (comm_op, 1, 2, 3))) == (True,)

    assert run(0, True, eq_comm((comm_op, 3, 2, 1), (comm_op, 1, 2, 3))) == (True,)
    assert run(0, y, eq_comm((comm_op, 3, y, 1), (comm_op, 1, 2, 3))) == (2,)
    assert run(0, (x, y), eq_comm((comm_op, x, y, 1), (comm_op, 1, 2, 3))) == (
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
    assert expected_res == set(
        run(0, (x, y, z), eq_comm((comm_op, x, y, z), (comm_op, 1, 2, 3)))
    )
    assert expected_res == set(
        run(
            0,
            (x, y, z),
            eq_comm(("div", 1, (comm_op, 1, 2, 3)), ("div", 1, (comm_op, x, y, z))),
        )
    )

    e1 = (comm_op, (comm_op, 1, x), y)
    e2 = (comm_op, 2, (comm_op, 3, 1))
    assert run(0, (x, y), eq_comm(e1, e2)) == ((3, 2),)

    e1 = ((comm_op, 3, 1),)
    e2 = ((comm_op, 1, x),)

    assert run(0, x, eq_comm(e1, e2)) == (3,)

    e1 = (2, (comm_op, 3, 1))
    e2 = (y, (comm_op, 1, x))

    assert run(0, (x, y), eq_comm(e1, e2)) == ((3, 2),)

    e1 = (comm_op, (comm_op, 1, x), y)
    e2 = (comm_op, 2, (comm_op, 3, 1))

    assert run(0, (x, y), eq_comm(e1, e2)) == ((3, 2),)


@pytest.mark.xfail(reason="`applyo`/`buildo` needs to be a constraint.", strict=True)
def test_eq_comm_object():
    x = var("x")

    fact(commutative, Add)
    fact(associative, Add)

    assert run(0, x, eq_comm(add(1, 2, 3), add(3, 1, x))) == (2,)
    assert set(run(0, x, eq_comm(add(1, 2), x))) == set((add(1, 2), add(2, 1)))
    assert set(run(0, x, eq_assoccomm(add(1, 2, 3), add(1, x)))) == set(
        (add(2, 3), add(3, 2))
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
            op_pred, [[1, 2, op], 3, [op, 4, [op, [op]]], [op, 5], 6, op, 7]
        )
    )
    exp_res = [[1, 2, op], 3, 4, [op], 5, 6, op, 7]
    assert res == exp_res


def test_assoc_args():
    op = "add"

    def op_pred(x):
        return x == op

    assert tuple(assoc_args(op, (1, 2, 3), 2)) == (
        ((op, 1, 2), 3),
        (1, (op, 2, 3)),
    )
    assert tuple(assoc_args(op, [1, 2, 3], 2)) == (
        [[op, 1, 2], 3],
        [1, [op, 2, 3]],
    )
    assert tuple(assoc_args(op, (1, 2, 3), 1)) == (
        ((op, 1), 2, 3),
        (1, (op, 2), 3),
        (1, 2, (op, 3)),
    )
    assert tuple(assoc_args(op, (1, 2, 3), 3)) == ((1, 2, 3),)

    f_rands = flatten_assoc_args(op_pred, (1, (op, 2, 3)))
    assert tuple(assoc_args(op, f_rands, 2, ctor=tuple)) == (
        ((op, 1, 2), 3),
        (1, (op, 2, 3)),
    )


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
        ((assoc_op, 1, 2), 3),
        (1, (assoc_op, 2, 3)),
    )
    assert run(0, x, eq_assoc_args(assoc_op, x, (1, 2, 3), n=2)) == (
        ((assoc_op, 1, 2), 3),
        (1, (assoc_op, 2, 3)),
    )

    assert run(0, x, eq_assoc_args(assoc_op, (1, 2, 3), x)) == (
        ((assoc_op, 1, 2), 3),
        (1, (assoc_op, 2, 3)),
        (1, 2, 3),
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
                assoc_op,
                (1, (assoc_op, 2, 3)),
                (1, (assoc_op, 2, 3)),
                no_ident=True,
            ),
        )
        == ()
    )

    assert (
        run(
            0,
            True,
            eq_assoc_args(
                assoc_op,
                (1, (assoc_op, 2, 3)),
                ((assoc_op, 1, 2), 3),
                no_ident=True,
            ),
        )
        == (True,)
    )


def test_eq_assoc():

    assoc_op = "assoc_op"

    associative.index.clear()
    associative.facts.clear()

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

    x = var()
    res = run(0, x, eq_assoc((assoc_op, 1, 2, 3), x, n=2))
    assert res == (
        (assoc_op, (assoc_op, 1, 2), 3),
        (assoc_op, 1, 2, 3),
        (assoc_op, 1, (assoc_op, 2, 3)),
    )

    res = run(0, x, eq_assoc(x, (assoc_op, 1, 2, 3), n=2))
    assert res == (
        (assoc_op, (assoc_op, 1, 2), 3),
        (assoc_op, 1, 2, 3),
        (assoc_op, 1, (assoc_op, 2, 3)),
    )

    y, z = var(), var()

    # Check results when both arguments are variables
    res = run(3, (x, y), eq_assoc(x, y))
    exp_res_form = (
        (etuple(assoc_op, x, y, z), etuple(assoc_op, etuple(assoc_op, x, y), z)),
        (x, y),
        (
            etuple(etuple(assoc_op, x, y, z)),
            etuple(etuple(assoc_op, etuple(assoc_op, x, y), z)),
        ),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert s is not False, (a, b)
        assert all(isvar(i) for i in reify((x, y, z), s))

    # Make sure it works with `cons`
    res = run(0, (x, y), eq_assoc(cons(x, y), (assoc_op, 1, 2, 3)))
    assert res == (
        (assoc_op, ((assoc_op, 1, 2), 3)),
        (assoc_op, (1, 2, 3)),
        (assoc_op, (1, (assoc_op, 2, 3))),
    )

    res = run(1, (x, y), eq_assoc(cons(x, y), (x, z, 2, 3)))
    assert res == ((assoc_op, ((assoc_op, z, 2), 3)),)

    # Don't use a predicate that can never succeed, e.g.
    # associative_2 = Relation("associative_2")
    # run(1, (x, y), eq_assoc(cons(x, y), (x, z), op_predicate=associative_2))

    # Nested expressions should work now
    expr1 = (assoc_op, 1, 2, (assoc_op, x, 5, 6))
    expr2 = (assoc_op, (assoc_op, 1, 2), 3, 4, 5, 6)
    assert run(0, x, eq_assoc(expr1, expr2, n=2)) == ((assoc_op, 3, 4),)


def test_assoc_flatten():

    add = "add"
    mul = "mul"

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)

    assert (
        run(
            0,
            True,
            assoc_flatten(
                (mul, 1, (add, 2, 3), (mul, 4, 5)), (mul, 1, (add, 2, 3), 4, 5)
            ),
        )
        == (True,)
    )

    x = var()
    assert (
        run(
            0,
            x,
            assoc_flatten((mul, 1, (add, 2, 3), (mul, 4, 5)), x),
        )
        == ((mul, 1, (add, 2, 3), 4, 5),)
    )

    assert (
        run(
            0,
            True,
            assoc_flatten(
                ("op", 1, (add, 2, 3), (mul, 4, 5)), ("op", 1, (add, 2, 3), (mul, 4, 5))
            ),
        )
        == (True,)
    )

    assert run(0, x, assoc_flatten(("op", 1, (add, 2, 3), (mul, 4, 5)), x)) == (
        ("op", 1, (add, 2, 3), (mul, 4, 5)),
    )


def test_eq_assoccomm():
    x, y = var(), var()

    ac = "commassoc_op"

    commutative.index.clear()
    commutative.facts.clear()

    fact(commutative, ac)
    fact(associative, ac)

    assert run(0, True, eq_assoccomm(1, 1)) == (True,)
    assert run(0, True, eq_assoccomm((1,), (1,))) == (True,)
    assert run(0, True, eq_assoccomm(x, (1,))) == (True,)
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
    # LHS variations
    assert set(run(0, x, eq_assoccomm(x, (ac, 1, (ac, 2, 3))))) == exp_res

    assert run(0, (x, y), eq_assoccomm((ac, (ac, 1, x), y), (ac, 2, (ac, 3, 1)))) == (
        (2, 3),
        (3, 2),
    )

    assert run(0, True, eq_assoccomm((ac, (ac, 1, 2), 3), (ac, 1, 2, 3))) == (True,)
    assert run(0, True, eq_assoccomm((ac, 3, (ac, 1, 2)), (ac, 1, 2, 3))) == (True,)
    assert run(0, True, eq_assoccomm((ac, 1, 1), ("other_op", 1, 1))) == ()

    assert run(0, x, eq_assoccomm((ac, 3, (ac, 1, 2)), (ac, 1, x, 3))) == (2,)

    # Both arguments unground
    op_lv = var()
    z = var()
    res = run(4, (x, y), eq_assoccomm(x, y))
    exp_res_form = (
        (etuple(op_lv, x, y), etuple(op_lv, y, x)),
        (y, y),
        (
            etuple(etuple(op_lv, x, y)),
            etuple(etuple(op_lv, y, x)),
        ),
        (
            etuple(op_lv, x, y, z),
            etuple(op_lv, etuple(op_lv, x, y), z),
        ),
    )

    for a, b in zip(res, exp_res_form):
        s = unify(a, b)
        assert (
            op_lv not in s
            or (s[op_lv],) in associative.facts
            or (s[op_lv],) in commutative.facts
        )
        assert s is not False, (a, b)
        assert all(isvar(i) for i in reify((x, y, z), s))


def test_assoccomm_algebra():

    add = "add"
    mul = "mul"

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    fact(commutative, add)
    fact(associative, add)
    fact(commutative, mul)
    fact(associative, mul)

    x, y = var(), var()

    pattern = (mul, (add, 1, x), y)  # (1 + x) * y
    expr = (mul, 2, (add, 3, 1))  # 2 * (3 + 1)

    assert run(0, (x, y), eq_assoccomm(pattern, expr)) == ((3, 2),)


def test_assoccomm_objects():

    commutative.index.clear()
    commutative.facts.clear()
    associative.index.clear()
    associative.facts.clear()

    fact(commutative, Add)
    fact(associative, Add)

    x = var()

    assert run(0, True, eq_assoccomm(add(1, 2, 3), add(3, 1, 2))) == (True,)
    assert run(0, x, eq_assoccomm(add(1, 2, 3), add(1, 2, x))) == (3,)
    assert run(0, x, eq_assoccomm(add(1, 2, 3), add(x, 2, 1))) == (3,)
