# flake8: noqa
"""kanren is a Python library for logic and relational programming."""
from unification import unify, reify, unifiable, var, isvar, vars, variables, Var

from .core import run, eq, conde, lall, lany
from .goals import (
    heado,
    tailo,
    conso,
    nullo,
    itero,
    appendo,
    rembero,
    permuteo,
    permuteq,
    membero,
    goalify,
)
from .facts import Relation, fact, facts
from .term import arguments, operator, term, unifiable_with_term

from ._version import get_versions

__version__ = get_versions()["version"]
del get_versions
