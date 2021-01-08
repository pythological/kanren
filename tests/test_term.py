from cons import cons
from etuples import etuple
from unification import reify, unify, var

from kanren.core import run
from kanren.term import applyo, arguments, operator, term, unifiable_with_term


@unifiable_with_term
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


class Op(object):
    def __init__(self, name):
        self.name = name


@arguments.register(Node)
def arguments_Node(t):
    return t.args


@operator.register(Node)
def operator_Node(t):
    return t.op


@term.register(Operator, (list, tuple))
def term_Op(op, args):
    return Node(op, args)


def test_applyo():
    x = var()
    assert run(0, x, applyo("add", (1, 2, 3), x)) == (("add", 1, 2, 3),)
    assert run(0, x, applyo(x, (1, 2, 3), ("add", 1, 2, 3))) == ("add",)
    assert run(0, x, applyo("add", x, ("add", 1, 2, 3))) == ((1, 2, 3),)

    a_lv, b_lv, c_lv = var(), var(), var()

    from operator import add

    assert run(0, c_lv, applyo(add, (1, 2), c_lv)) == (3,)
    assert run(0, c_lv, applyo(add, etuple(1, 2), c_lv)) == (3,)
    assert run(0, c_lv, applyo(add, a_lv, c_lv)) == (cons(add, a_lv),)

    for obj in (
        (1, 2, 3),
        (add, 1, 2),
        [1, 2, 3],
        [add, 1, 2],
        etuple(1, 2, 3),
        etuple(add, 1, 2),
    ):
        o_rator, o_rands = operator(obj), arguments(obj)
        assert run(0, a_lv, applyo(o_rator, o_rands, a_lv)) == (term(o_rator, o_rands),)
        # Just acts like `conso` here
        assert run(0, a_lv, applyo(o_rator, a_lv, obj)) == (arguments(obj),)
        assert run(0, a_lv, applyo(a_lv, o_rands, obj)) == (operator(obj),)

    # Just acts like `conso` here, too
    assert run(0, c_lv, applyo(a_lv, b_lv, c_lv)) == (cons(a_lv, b_lv),)

    # with pytest.raises(ConsError):
    assert run(0, a_lv, applyo(a_lv, b_lv, object())) == ()
    assert run(0, a_lv, applyo(1, 2, a_lv)) == ()


def test_applyo_object():
    x = var()
    assert run(0, x, applyo(Add, (1, 2, 3), x)) == (add(1, 2, 3),)
    assert run(0, x, applyo(x, (1, 2, 3), add(1, 2, 3))) == (Add,)
    assert run(0, x, applyo(Add, x, add(1, 2, 3))) == ((1, 2, 3),)


def test_unifiable_with_term():
    add = Operator("add")
    t = Node(add, (1, 2))

    assert arguments(t) == (1, 2)
    assert operator(t) == add
    assert term(operator(t), arguments(t)) == t

    x = var()
    s = unify(Node(add, (1, x)), Node(add, (1, 2)), {})

    assert s == {x: 2}
    assert reify(Node(add, (1, x)), s) == Node(add, (1, 2))
