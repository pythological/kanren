from collections.abc import Sequence

from unification import unify, reify
from unification.core import _unify, _reify

from cons.core import cons

from etuples import rator as operator, rands as arguments, apply as term


@term.register(object, Sequence)
def term_Sequence(rator, rands):
    # Overwrite the default `apply` dispatch function and make it preserve
    # types
    res = cons(rator, rands)
    return res


def unifiable_with_term(cls):
    _reify.add((cls, dict), reify_term)
    _unify.add((cls, cls, dict), unify_term)
    return cls


def reify_term(obj, s):
    op, args = operator(obj), arguments(obj)
    op = reify(op, s)
    args = reify(args, s)
    new = term(op, args)
    return new


def unify_term(u, v, s):
    u_op, u_args = operator(u), arguments(u)
    v_op, v_args = operator(v), arguments(v)
    s = unify(u_op, v_op, s)
    if s is not False:
        s = unify(u_args, v_args, s)
    return s
