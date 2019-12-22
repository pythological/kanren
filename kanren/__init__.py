# flake8: noqa
"""kanren is a Python library for logic and relational programming."""
from __future__ import absolute_import

from unification import unify, reify, unifiable, var, isvar, vars, variables, Var

from .core import run, eq, conde, lall, lany
from .goals import seteq, permuteq, goalify, membero
from .facts import Relation, fact, facts
from .term import arguments, operator, term, unifiable_with_term

from ._version import get_versions

__version__ = get_versions()["version"]
del get_versions
