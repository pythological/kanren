from itertools import permutations

from unification import var, unify
from unification.core import _reify

from cons import cons

from kanren import run, eq
from kanren.core import lall, goaleval
from kanren.constraints import ConstrainedState, DisequalityStore, neq, ConstrainedVar


def lconj(*goals):
    return goaleval(lall(*goals))


def test_kanrenstate():

    a_lv, b_lv = var(), var()

    ks = ConstrainedState()

    assert repr(ks) == "ConstrainedState({}, {})"

    assert ks == {}
    assert {} == ks
    assert not ks == {a_lv: 1}
    assert not ks == ConstrainedState({a_lv: 1})

    assert unify(1, 1, ks) is not None
    assert unify(1, 2, ks) is False

    assert unify(b_lv, a_lv, ks)
    assert unify(a_lv, b_lv, ks)
    assert unify(a_lv, b_lv, ks)

    # Now, try that with a constraint (that's never used).
    ks.constraints[DisequalityStore] = DisequalityStore({a_lv: {1}})

    assert not ks == {a_lv: 1}
    assert not ks == ConstrainedState({a_lv: 1})

    assert unify(1, 1, ks) is not None
    assert unify(1, 2, ks) is False

    assert unify(b_lv, a_lv, ks)
    assert unify(a_lv, b_lv, ks)
    assert unify(a_lv, b_lv, ks)


def test_reify():
    var_a = var("a")

    ks = ConstrainedState()
    assert repr(ConstrainedVar(var_a, ks)) == "~a: {}"

    de = DisequalityStore({var_a: {1, 2}})
    ks.constraints[DisequalityStore] = de

    assert repr(de) == "ConstraintStore(=/=: {~a: {1, 2}})"
    assert de.constraints_str(var()) == ""

    assert repr(ConstrainedVar(var_a, ks)) == "~a: {=/= {1, 2}}"

    # TODO: Make this work with `reify` when `var('a')` isn't in `ks`.
    assert isinstance(_reify(var_a, ks), ConstrainedVar)
    assert repr(_reify(var_a, ks)) == "~a: {=/= {1, 2}}"


def test_ConstraintStore():
    a_lv, b_lv = var(), var()
    assert DisequalityStore({a_lv: {1}}) == DisequalityStore({a_lv: {1}})
    assert DisequalityStore({a_lv: {1}}) != DisequalityStore({a_lv: {1}, b_lv: {}})

    assert a_lv in DisequalityStore({a_lv: {1}})


def test_ConstrainedVar():

    a_lv = var()
    a_clv = ConstrainedVar(a_lv, ConstrainedState())

    assert a_lv == a_clv
    assert a_clv == a_lv

    assert hash(a_lv) == hash(a_clv)

    assert a_lv in {a_clv}
    assert a_clv in {a_lv}


def test_disequality():

    a_lv, b_lv = var(), var()

    ks = ConstrainedState()
    de = DisequalityStore({a_lv: {1}})
    ks.constraints[DisequalityStore] = de

    assert unify(a_lv, 1, ks) is False

    ks = unify(a_lv, b_lv, ks)
    assert unify(b_lv, 1, ks) is False

    res = list(lconj(neq({}, 1))({}))
    assert len(res) == 1

    res = list(lconj(neq(1, {}))({}))
    assert len(res) == 1

    res = list(lconj(neq({}, {}))({}))
    assert len(res) == 0

    res = list(lconj(neq(a_lv, 1))({}))
    assert len(res) == 1
    assert isinstance(res[0], ConstrainedState)
    assert res[0].constraints[DisequalityStore].lvar_constraints[a_lv] == {1}

    res = list(lconj(neq(1, a_lv))({}))
    assert len(res) == 1
    assert isinstance(res[0], ConstrainedState)
    assert res[0].constraints[DisequalityStore].lvar_constraints[a_lv] == {1}

    res = list(lconj(neq(a_lv, 1), neq(a_lv, 2), neq(a_lv, 1))({}))
    assert len(res) == 1
    assert isinstance(res[0], ConstrainedState)
    assert res[0].constraints[DisequalityStore].lvar_constraints[a_lv] == {1, 2}

    res = list(lconj(neq(a_lv, 1), eq(a_lv, 2))({}))
    assert len(res) == 1
    assert isinstance(res[0], ConstrainedState)
    # The constrained variable is already ground and satisfies the constraint,
    # so it should've been removed from the store
    assert a_lv not in res[0].constraints[DisequalityStore].lvar_constraints
    assert res[0][a_lv] == 2

    res = list(lconj(eq(a_lv, 1), neq(a_lv, 1))({}))
    assert res == []

    q_lv, c_lv = var(), var()

    goal_sets = [
        ([neq(a_lv, 1)], 1),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, [])], 0),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, b_lv), eq(b_lv, [])], 0),
        ([neq([1], cons(1, a_lv)), eq(a_lv, b_lv), eq(b_lv, [])], 0),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, b_lv), eq(b_lv, tuple())], 1),
        ([neq([1], cons(1, a_lv)), eq(a_lv, b_lv), eq(b_lv, tuple())], 1),
        ([neq(a_lv, 1), eq(a_lv, 1)], 0),
        ([neq(a_lv, 1), eq(b_lv, 1), eq(a_lv, b_lv)], 0),
        ([neq(a_lv, 1), eq(b_lv, 1), eq(a_lv, b_lv)], 0),
        ([neq(a_lv, b_lv), eq(b_lv, c_lv), eq(c_lv, a_lv)], 0),
    ]

    for i, (goal, num_results) in enumerate(goal_sets):
        # The order of goals should not matter, so try them all
        for goal_ord in permutations(goal):

            res = list(lconj(*goal_ord)({}))
            assert len(res) == num_results

            res = list(lconj(*goal_ord)(ConstrainedState()))
            assert len(res) == num_results

            assert len(run(0, q_lv, *goal_ord)) == num_results
