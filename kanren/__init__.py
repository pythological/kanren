# flake8: noqa
"""kanren is a Python library for logic and relational programming."""
from importlib.metadata import version

from unification import Var, isvar, reify, unifiable, unify, var, variables, vars

from .core import conde, eq, lall, lany, run
from .facts import Relation, fact, facts
from .goals import (
    appendo,
    conso,
    heado,
    itero,
    membero,
    nullo,
    permuteo,
    permuteq,
    rembero,
    tailo,
)
from .term import arguments, operator, term, unifiable_with_term


__version__ = version("miniKanren")
