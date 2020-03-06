from abc import ABCMeta
from operator import length_hint
from collections.abc import Mapping, Callable

from multipledispatch import dispatch

from unification.core import reify, _unify, _reify, construction_sentinel
from unification.variable import isvar

from cons.core import cons, ConsError, ProperSequence

from etuples import apply, rands as arguments, rator as operator

from .core import eq, lall, shallow_ground_order_key
from .goals import conso


class TermMetaType(ABCMeta):
    """A meta type that can be used to check for `operator`/`arguments` support."""

    def __instancecheck__(self, o):
        o_type = type(o)
        if (
            isinstance(o, ProperSequence)
            or any(
                issubclass(o_type, k) for k in operator.funcs.keys() if k[0] != object
            )
        ) and length_hint(o, 1) > 0:
            return True
        return False

    def __subclasscheck__(self, o_type):
        if issubclass(o_type, ProperSequence) or any(
            issubclass(o_type, k) for k in operator.funcs.keys() if k[0] != object
        ):
            return True
        return False


class TermType(metaclass=TermMetaType):
    pass


def applyo(o_rator, o_rands, obj):
    """Construct a goal that relates an object to the application of its (ope)rator to its (ope)rands.

    In other words, this is the relation `op(*args) == obj`.  It uses the
    `rator`, `rands`, and `apply` dispatch functions from `etuples`, so
    implement/override those to get the desired behavior.

    """

    def applyo_goal(S):
        nonlocal o_rator, o_rands, obj

        o_rator_rf, o_rands_rf, obj_rf = reify((o_rator, o_rands, obj), S)

        if not isvar(obj_rf):

            # We should be able to use this goal with *any* arguments, so
            # fail when the ground operations fail/err.
            try:
                obj_rator, obj_rands = operator(obj_rf), arguments(obj_rf)
            except (ConsError, NotImplementedError):
                return

            # The object's rator + rands should be the same as the goal's
            yield from lall(eq(o_rator_rf, obj_rator), eq(o_rands_rf, obj_rands))(S)

        elif isvar(o_rands_rf) or isvar(o_rator_rf):
            # The object and at least one of the rand, rators is a logic
            # variable, so let's just assert a `cons` relationship between
            # them
            yield from conso(o_rator_rf, o_rands_rf, obj_rf)(S)
        else:
            # The object is a logic variable, but the rator and rands aren't.
            # We assert that the object is the application of the rand and
            # rators.
            try:
                obj_applied = term(o_rator_rf, o_rands_rf)
            except (ConsError, NotImplementedError):
                return
            yield from eq(obj_rf, obj_applied)(S)

    return applyo_goal


@dispatch(object, ProperSequence)
def term(rator, rands):
    # Overwrite the default `apply` dispatch function and make it preserve
    # types
    res = cons(rator, rands)
    return res


@term.register(Callable, ProperSequence)
def term_ExpressionTuple(rator, rands):
    return apply(rator, rands)


def unifiable_with_term(cls):
    _reify.add((cls, Mapping), reify_term)
    _unify.add((cls, cls, Mapping), unify_term)
    return cls


def reify_term(obj, s):
    op, args = operator(obj), arguments(obj)
    op = yield _reify(op, s)
    args = yield _reify(args, s)
    yield construction_sentinel
    yield term(op, args)


def unify_term(u, v, s):
    u_op, u_args = operator(u), arguments(u)
    v_op, v_args = operator(v), arguments(v)
    s = yield _unify(u_op, v_op, s)
    if s is not False:
        s = yield _unify(u_args, v_args, s)
    yield s


@shallow_ground_order_key.register(Mapping, TermType)
def shallow_ground_order_key_TermType(S, x):
    if length_hint(x, 1) > 0:
        return shallow_ground_order_key.dispatch(type(S), object)(
            S, cons(operator(x), arguments(x))
        )
    else:
        return shallow_ground_order_key.dispatch(type(S), object)(S, x)
