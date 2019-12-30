from unification import var, unify, reify

from kanren.term import term, operator, arguments, unifiable_with_term


class Op(object):
    def __init__(self, name):
        self.name = name


@unifiable_with_term
class MyTerm(object):
    def __init__(self, op, arguments):
        self.op = op
        self.arguments = arguments

    def __eq__(self, other):
        return self.op == other.op and self.arguments == other.arguments


@arguments.register(MyTerm)
def arguments_MyTerm(t):
    return t.arguments


@operator.register(MyTerm)
def operator_MyTerm(t):
    return t.op


@term.register(Op, (list, tuple))
def term_Op(op, args):
    return MyTerm(op, args)


def test_unifiable_with_term():
    add = Op("add")
    t = MyTerm(add, (1, 2))

    assert arguments(t) == (1, 2)
    assert operator(t) == add
    assert term(operator(t), arguments(t)) == t

    x = var()
    s = unify(MyTerm(add, (1, x)), MyTerm(add, (1, 2)), {})

    assert s == {x: 2}
    assert reify(MyTerm(add, (1, x)), s) == MyTerm(add, (1, 2))
