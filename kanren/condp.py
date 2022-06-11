from itertools import tee
from typing import Mapping, Optional, Sequence, Tuple, Union

from cons import car, cdr
from toolz import interleave
from unification import reify
from unification.utils import transitive_get as walk

from .core import lall, lconj_seq, ldisj_seq


def collect(s: Mapping, f_lists: Optional[Sequence] = None):
    """A function that produces suggestions (for `condp`) based on the values of
    partially reified terms.

    This goal takes a list of suggestion function, variable pairs lists and
    evaluates them at their current, partially reified variable values
    (i.e. ``f(walk(x, s))`` for pair ``(f, x)``).  Each evaluated function should
    return ``None``, a string label in a corresponding `condp` clause, or the
    string ``"use-maybe"``.

    Each list of suggestion functions is evaluated in order, their output is
    concatenated, and, if the output contains a ``"use-maybe"`` string, the
    next list of suggestion functions is evaluated.

    Parameters
    ==========
    s
        miniKanren state.
    f_lists
        A collection of function + variable pair collections (e.g.
        ``[[(f0, x0), ...], ..., [(f, x), ...]]``).
    """
    if isinstance(f_lists, Sequence):
        # TODO: Would be cool if this was lazily evaluated, no?
        # Seems like this whole thing would have to become a generator
        # function, though.
        ulos = ()
        # ((f0, x0), ...), ((f, x), ...)
        for f_list in f_lists:
            f, args = car(f_list), cdr(f_list)
            _ulos = f(*(walk(a, s) for a in args))
            ulos += _ulos
            if "use-maybe" not in _ulos:
                return ulos
        return ulos
    else:
        return ()


def condp(global_sugs: Tuple, branches: Union[Sequence, Mapping]):
    """A goal generator that produces a `conde`-like relation driven by
    suggestions potentially derived from partial miniKanren state values.

    From [1]_.

    Parameters
    ==========
    global_sugs
        A tuple containing tuples of suggestion functions and their
        logic variable arguments.  Each suggestion function is evaluated
        using the reified versions of its corresponding logic variables (i.e.
        their "projected" values).  Each suggestion function is expected to
        return a tuple of branch labels corresponding to the keys in
        `branches`.
    branches
        Sequence or mapping of string labels--for each branch in a conde-like
        goal--to a tuple of goals pairs.


    .. [1] Boskin, Benjamin Strahan, Weixi Ma, David Thrane Christiansen, and Daniel
    P. Friedman, "A Surprisingly Competitive Conditional Operator."

    """
    if isinstance(branches, Mapping):
        branches_: Sequence = tuple(branches.items())
    else:
        branches_ = branches

    def _condp(s):
        global_los = collect(s, global_sugs)
        yield from ldisj_seq(lconj_seq(g) for k, g in branches_ if k in global_los)(s)

    return _condp


def collectseq(branch_s: Mapping, f_lists: Optional[Sequence] = None):
    """A version of `collect` that takes a `dict` of branches-to-states.

    Parameters
    ==========
    branch_s
        Branch labels to miniKanren state/replacements dictionaries.
    f_lists
        A collection of function + variable pair collections (e.g.
        ``[[(f0, x0), ...], ..., [(f, x), ...]]``).
    """
    if isinstance(f_lists, Sequence):
        ulos = ()
        for f_list in f_lists:
            f, args = f_list
            _ulos = f({k: reify(args, s) for k, s in branch_s.items()})
            ulos += _ulos
            if "use-maybe" not in _ulos:
                return ulos
        return ulos
    else:
        return ()


def condpseq(branches: Union[Sequence[Sequence], Mapping]):
    r"""An experimental version of `condp` that passes branch-state-reified
    maps to branch-specific suggestion functions.

    In other words, each branch-specific suggestion function is passed a `dict`
    with branch-label keys and the its function arguments are reified against
    the state resulting from said branch.

    .. note::

        Only previously evaluated branches will show up in these `dict`\s, so
        branch order will determine the information available to each suggestion
        function.

    Parameters
    ==========
    branches
        Ordered map or a sequence of sequences mapping string labels--for each
        branch in a `conde`-like goal--to a tuple starting with a single
        suggestion function followed by the branch goals.

    """
    if isinstance(branches, Mapping):
        branches_: Sequence = tuple(branches.items())
    else:
        branches_ = branches

    def _condpseq(s, __bm=branches_):
        __bm, local_items = tee(__bm)

        # Provide each branch-specific suggestion function a copy of the state
        # after the preceding branch's goals have been evaluated.
        def f(items):
            los = set()
            branch_s = {}
            for k, goals_branch_sugs in local_items:
                # Branch suggestions can be `None` and all branch
                # goals will be added.
                branch_sugs = car(goals_branch_sugs)
                goals = cdr(goals_branch_sugs)

                if branch_sugs:
                    # We only expect one suggestion function per-branch.
                    branch_sugs = (branch_sugs,)
                    los |= set(collectseq(branch_s or {k: s}, branch_sugs))

                if branch_sugs is None or k in los:
                    # TODO: Refactor!
                    a, b = tee(lall(*goals)(s))
                    branch_s[k] = next(a)
                    yield b

                branch_s.setdefault(k, None)

        yield from interleave(f(local_items))

    return _condpseq
