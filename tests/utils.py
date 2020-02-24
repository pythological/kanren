from kanren.term import arguments, operator


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

    def __call__(self, *args):
        return Node(self, args)

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name

    def __hash__(self):
        return hash((type(self), self.name))

    def __str__(self):
        return self.name

    __repr__ = __str__


Add = Operator("add")
Mul = Operator("mul")


@arguments.register(Node)
def arguments_Node(t):
    return t.args


@operator.register(Node)
def operator_Node(t):
    return t.op


# @term.register(Operator, Sequence)
# def term_Operator(op, args):
#     return Node(op, args)
