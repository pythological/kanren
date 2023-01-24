from cons import car, cons
from cons.core import ConsNull, ConsPair
from unification import isvar, var

from kanren.condp import condp, condpseq
from kanren.core import Zzz, conde, eq, run
from kanren.goals import nullo


def test_condp():
    """Test `condp` using the example from [1]_.

    .. [1] Boskin, Benjamin Strahan, Weixi Ma, David Thrane Christiansen, and Daniel
    P. Friedman, "A Surprisingly Competitive Conditional Operator."

    """

    def _ls_keys(ls):
        if isvar(ls):
            return ("use-maybe",)
        elif isinstance(ls, ConsNull):
            return ("BASE",)
        elif isinstance(ls, ConsPair):
            return ("KEEP", "SWAP")
        else:
            return ()

    def _o_keys(o):
        if isvar(o):
            return ("BASE", "KEEP", "SWAP")
        elif isinstance(o, ConsNull):
            return ("BASE",)
        elif isinstance(o, ConsPair):
            if isvar(car(o)) or "novel" == car(o):
                return ("KEEP", "SWAP")
            else:
                return ("KEEP",)
        else:
            return ()

    def swap_somep(ls, o):
        a, d, res = var(), var(), var()
        res = condp(
            ((_ls_keys, ls), (_o_keys, o)),
            {
                "BASE": (nullo(ls), nullo(o)),
                "KEEP": (
                    eq(cons(a, d), ls),
                    eq(cons(a, res), o),
                    Zzz(swap_somep, d, res),
                ),
                "SWAP": (
                    eq(cons(a, d), ls),
                    eq(cons("novel", res), o),
                    Zzz(swap_somep, d, res),
                ),
            },
        )
        return res

    def swap_someo(ls, o):
        """The original `conde` version."""
        a, d, res = var(), var(), var()
        return conde(
            [nullo(ls), nullo(o)],
            [eq(cons(a, d), ls), eq(cons(a, res), o), Zzz(swap_someo, d, res)],
            [eq(cons(a, d), ls), eq(cons("novel", res), o), Zzz(swap_someo, d, res)],
        )

    q, r = var("q"), var("r")

    condp_res = run(0, [q, r], swap_somep(q, ["novel", r]))

    assert len(condp_res) == 4
    assert condp_res[0][0][0] == "novel"
    assert isvar(condp_res[0][0][1])
    assert isvar(condp_res[0][1])

    assert isvar(condp_res[1][0][0])
    assert isvar(condp_res[1][0][1])
    assert isvar(condp_res[1][1])

    assert condp_res[2][0][0] == "novel"
    assert isvar(condp_res[2][0][1])
    assert condp_res[2][1] == "novel"

    assert isvar(condp_res[3][0][0])
    assert isvar(condp_res[3][0][1])
    assert condp_res[3][1] == "novel"


def test_condpseq():
    def base_sug(a_branches):
        if a_branches["BRANCH1"] == 1:
            return ("BRANCH3",)
        else:
            return (
                "BRANCH2",
                "BRANCH3",
            )

    def test_rel(a):
        return condpseq(
            {
                "BRANCH1": (None, eq(a, 1)),
                "BRANCH2": ((base_sug, a), eq(a, 2)),
                "BRANCH3": (None, eq(a, 3)),
            }
        )

    q = var("q")

    res = run(0, [q], test_rel(q))

    assert res == ([1], [3])
