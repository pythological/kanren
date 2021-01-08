from itertools import permutations

from cons import cons
from pytest import raises
from unification import reify, unify, var
from unification.core import _reify, stream_eval

from kanren import conde, eq, run
from kanren.constraints import (
    ConstrainedState,
    ConstrainedVar,
    DisequalityStore,
    isinstanceo,
    neq,
    typeo,
)
from kanren.core import lconj
from kanren.goals import membero


def test_ConstrainedState():

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

    ks = ConstrainedState(
        {a_lv: 1}, constraints={DisequalityStore: DisequalityStore({b_lv: {1}})}
    )
    ks_2 = ks.copy()
    assert ks == ks_2
    assert ks is not ks_2
    assert ks.constraints is not ks_2.constraints
    assert ks.constraints[DisequalityStore] is not ks_2.constraints[DisequalityStore]
    assert (
        ks.constraints[DisequalityStore].lvar_constraints[b_lv]
        == ks_2.constraints[DisequalityStore].lvar_constraints[b_lv]
    )
    assert (
        ks.constraints[DisequalityStore].lvar_constraints[b_lv]
        is not ks_2.constraints[DisequalityStore].lvar_constraints[b_lv]
    )


def test_reify():
    var_a = var("a")

    ks = ConstrainedState()
    assert repr(ConstrainedVar(var_a, ks)) == "~a: {}"

    de = DisequalityStore({var_a: {1, 2}})
    ks.constraints[DisequalityStore] = de

    assert repr(de) == "ConstraintStore(neq: {~a: {1, 2}})"
    assert de.constraints_str(var()) == ""

    assert repr(ConstrainedVar(var_a, ks)) == "~a: {neq {1, 2}}"

    # TODO: Make this work with `reify` when `var('a')` isn't in `ks`.
    assert isinstance(reify(var_a, ks), ConstrainedVar)
    assert repr(stream_eval(_reify(var_a, ks))) == "~a: {neq {1, 2}}"


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


def test_disequality_basic():

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


def test_disequality():

    a_lv, b_lv = var(), var()
    q_lv, c_lv = var(), var()

    goal_sets = [
        ([neq(a_lv, 1)], 1),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, [])], 0),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, b_lv), eq(b_lv, [])], 0),
        ([neq([1], cons(1, a_lv)), eq(a_lv, b_lv), eq(b_lv, [])], 0),
        # TODO FIXME: This one won't work due to an ambiguity in `cons`.
        # (
        #     [
        #         neq([1], cons(1, a_lv)),
        #         eq(a_lv, b_lv),
        #         # Both make `cons` produce a list
        #         conde([eq(b_lv, None)], [eq(b_lv, [])]),
        #     ],
        #     0,
        # ),
        ([neq(cons(1, a_lv), [1]), eq(a_lv, b_lv), eq(b_lv, tuple())], 1),
        ([neq([1], cons(1, a_lv)), eq(a_lv, b_lv), eq(b_lv, tuple())], 1),
        (
            [
                neq([1], cons(1, a_lv)),
                eq(a_lv, b_lv),
                # The first should fail, the second should succeed
                conde([eq(b_lv, [])], [eq(b_lv, tuple())]),
            ],
            1,
        ),
        ([neq(a_lv, 1), eq(a_lv, 1)], 0),
        ([neq(a_lv, 1), eq(b_lv, 1), eq(a_lv, b_lv)], 0),
        ([neq(a_lv, 1), eq(b_lv, 1), eq(a_lv, b_lv)], 0),
        ([neq(a_lv, b_lv), eq(b_lv, c_lv), eq(c_lv, a_lv)], 0),
    ]

    for i, (goal, num_results) in enumerate(goal_sets):
        # The order of goals should not matter, so try them all
        for goal_ord in permutations(goal):

            res = list(lconj(*goal_ord)({}))
            assert len(res) == num_results, (i, goal_ord)

            res = list(lconj(*goal_ord)(ConstrainedState()))
            assert len(res) == num_results, (i, goal_ord)

            assert len(run(0, q_lv, *goal_ord)) == num_results, (i, goal_ord)


def test_typeo_basic():
    a_lv, q_lv = var(), var()

    assert run(0, q_lv, typeo(q_lv, int)) == (q_lv,)
    assert run(0, q_lv, typeo(1, int)) == (q_lv,)
    assert run(0, q_lv, typeo(1, str)) == ()
    assert run(0, q_lv, typeo("hi", str)) == (q_lv,)
    assert run(0, q_lv, typeo([], q_lv)) == (q_lv,)
    # Invalid second arg type (i.e. not a type)
    assert run(0, q_lv, typeo(1, 1)) == ()
    assert run(0, q_lv, membero(q_lv, (1, "cat", 2.2, "hat")), typeo(q_lv, str)) == (
        "cat",
        "hat",
    )

    with raises(ValueError):
        run(0, q_lv, typeo(a_lv, str), typeo(a_lv, int))


def test_typeo():
    a_lv, b_lv, q_lv = var(), var(), var()

    goal_sets = [
        # Logic variable instance type that's immediately ground in another
        # goal
        ([typeo(q_lv, int), eq(q_lv, 1)], (1,)),
        # Use an unhashable constrained term
        ([typeo(q_lv, list), eq(q_lv, [])], ([],)),
        # TODO: A constraint parameter that is never ground
        # ([typeo(a_lv, q_lv), eq(a_lv, 1)], (int,)),
        # A non-ground, non-logic variable instance argument that changes type
        # when ground
        ([typeo(cons(1, a_lv), list), eq(a_lv, [])], (q_lv,)),
        # Logic variable instance and type arguments
        ([typeo(q_lv, int), eq(b_lv, 1), eq(b_lv, q_lv)], (1,)),
        # The same, but with `conde`
        (
            [
                typeo(q_lv, int),
                # One succeeds, one fails
                conde([eq(b_lv, 1)], [eq(b_lv, "hi")]),
                eq(b_lv, q_lv),
            ],
            (1,),
        ),
        # Logic variable instance argument that's eventually grounded to a
        # mismatched instance type through another logic variable
        ([typeo(q_lv, int), eq(b_lv, 1.0), eq(b_lv, q_lv)], ()),
        # Logic variable type argument that's eventually grounded to a
        # mismatched instance type through another logic variable (i.e. both
        # arguments are ground to `int` types)
        ([typeo(q_lv, b_lv), eq(b_lv, int), eq(b_lv, q_lv)], ()),
        # Logic variable type argument that's eventually grounded to a
        # mismatched instance type through another logic variable (i.e. both
        # arguments are ground to the value `1`, which violates the second
        # argument type expectations)
        ([typeo(q_lv, b_lv), eq(b_lv, 1), eq(b_lv, q_lv)], ()),
        # Check a term that's unground by ground enough for this constraint
        ([typeo(a_lv, tuple), eq([(b_lv,)], a_lv)], ()),
    ]

    for i, (goal, expected) in enumerate(goal_sets):
        for goal_ord in permutations(goal):
            res = run(0, q_lv, *goal_ord)
            assert res == expected, (i, goal_ord)


def test_instanceo_basic():
    q_lv = var()

    assert run(0, q_lv, isinstanceo(q_lv, int)) == (q_lv,)
    assert run(0, q_lv, isinstanceo(1, int)) == (q_lv,)
    assert run(0, q_lv, isinstanceo(1, object)) == (q_lv,)
    # NOTE: Not currently supported.
    # assert run(0, q_lv, isinstanceo(1, (int, object))) == (q_lv,)
    assert run(0, q_lv, isinstanceo(1, str)) == ()
    # NOTE: Not currently supported.
    # assert run(0, q_lv, isinstanceo(1, (str, list))) == ()
    assert run(0, q_lv, isinstanceo("hi", str)) == (q_lv,)
    # Invalid second arg type (i.e. not a type)
    assert run(0, q_lv, isinstanceo(1, 1)) == ()


def test_instanceo():
    b_lv, q_lv = var(), var()

    goal_sets = [
        # Logic variable instance type that's immediately ground in another
        # goal
        ([isinstanceo(q_lv, list), eq(q_lv, [])], ([],)),
        # Logic variable in the type argument that's eventually unified with
        # a valid type for the given instance argument
        ([isinstanceo([], q_lv), eq(q_lv, list)], (list,)),
        # Logic variable type argument that's eventually reified to a tuple
        # containing a valid type for the instance argument
        # NOTE: Not currently supported.
        # (
        #     [isinstanceo([], q_lv), eq(q_lv, (int, b_lv)), eq(b_lv, list)],
        #     ((int, list),),
        # ),
        # A non-ground, non-logic variable instance argument that changes type
        # when ground
        ([isinstanceo(cons(1, q_lv), list), eq(q_lv, [])], ([],)),
        # Logic variable instance argument that's eventually grounded through
        # another logic variable
        ([isinstanceo(q_lv, int), eq(b_lv, 1), eq(b_lv, q_lv)], (1,)),
        # The same, but with `conde`
        (
            [
                isinstanceo(q_lv, int),
                # One succeeds, one fails
                conde([eq(b_lv, 1)], [eq(b_lv, "hi")]),
                eq(b_lv, q_lv),
            ],
            (1,),
        ),
        # Logic variable instance argument that's eventually grounded to a
        # mismatched instance type through another logic variable
        ([isinstanceo(q_lv, int), eq(b_lv, 1.0), eq(b_lv, q_lv)], ()),
        # Logic variable type argument that's eventually grounded to a
        # mismatched instance type through another logic variable (i.e. both
        # arguments are ground to `int` types)
        ([isinstanceo(q_lv, b_lv), eq(b_lv, int), eq(b_lv, q_lv)], ()),
        # Logic variable type argument that's eventually grounded to a
        # mismatched instance type through another logic variable (i.e. both
        # arguments are ground to the value `1`, which violates the second
        # argument type expectations)
        ([isinstanceo(q_lv, b_lv), eq(b_lv, 1), eq(b_lv, q_lv)], ()),
        # Check a term that's unground by ground enough for this constraint
        ([isinstanceo(q_lv, tuple), eq([(b_lv,)], q_lv)], ()),
    ]

    for i, (goal, expected) in enumerate(goal_sets):
        for goal_ord in permutations(goal):
            res = run(0, q_lv, *goal_ord)
            assert res == expected, (i, goal_ord)
