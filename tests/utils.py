import random

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


def generate_term(ops, args, i=10, gen_fn=None):

    if gen_fn is not None:

        gen_res = gen_fn(ops, args, i)

        if gen_res is not None:
            return gen_res

    g_op = random.choice(ops)

    if i > 0:
        num_sub_graphs = len(args) // 2
    else:
        num_sub_graphs = 0

    g_args = random.sample(args, len(args) - num_sub_graphs)
    g_args += [
        generate_term(ops, args, i=i - 1, gen_fn=gen_fn) for s in range(num_sub_graphs)
    ]

    random.shuffle(g_args)

    return [g_op] + list(g_args)
