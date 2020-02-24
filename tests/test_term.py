from unification import var, unify, reify

from cons import cons
from etuples import etuple

from kanren.core import run
from kanren.term import applyo, arguments, operator, term

from tests.utils import Node, Operator, Add


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
    assert run(0, x, applyo(Add, (1, 2, 3), x)) == (Add(1, 2, 3),)
    assert run(0, x, applyo(x, (1, 2, 3), Add(1, 2, 3))) == (Add,)
    assert run(0, x, applyo(Add, x, Add(1, 2, 3))) == ((1, 2, 3),)


def test_term_dispatch():

    t = Node(Add, (1, 2))

    assert arguments(t) == (1, 2)
    assert operator(t) == Add
    assert term(operator(t), arguments(t)) == t


def test_unifiable_with_term():
    from kanren.term import unifiable_with_term

    @unifiable_with_term
    class NewNode(Node):
        pass

    class NewOperator(Operator):
        def __call__(self, *args):
            return NewNode(self, args)

    NewAdd = NewOperator("newadd")

    x = var()
    s = unify(NewNode(NewAdd, (1, x)), NewNode(NewAdd, (1, 2)), {})

    assert s == {x: 2}
    assert reify(NewNode(NewAdd, (1, x)), s) == NewNode(NewAdd, (1, 2))
