"""
Zebra puzzle as published in Life International in 1962.
https://en.wikipedia.org/wiki/Zebra_Puzzle
"""
from dataclasses import dataclass, field
from typing import Union

from unification import Var, unifiable, var, vars

from kanren import conde, eq, lall, membero, run


@unifiable
@dataclass
class House:
    nationality: Union[str, Var] = field(default_factory=var)
    drink: Union[str, Var] = field(default_factory=var)
    animal: Union[str, Var] = field(default_factory=var)
    cigarettes: Union[str, Var] = field(default_factory=var)
    color: Union[str, Var] = field(default_factory=var)


def righto(right, left, houses):
    """Express that `right` is on the right of `left` among all the houses."""
    neighbors = tuple(zip(houses[:-1], houses[1:]))
    return membero((left, right), neighbors)


def nexto(a, b, houses):
    """Express that `a` and `b` are next to each other."""
    return conde([righto(a, b, houses)], [righto(b, a, houses)])


# And now for the riddle
houses = vars(5)
goals = lall(
    membero(House("Englishman", color="red"), houses),
    membero(House("Spaniard", animal="dog"), houses),
    membero(House(drink="coffee", color="green"), houses),
    membero(House("Ukrainian", drink="tea"), houses),
    righto(House(color="green"), House(color="ivory"), houses),
    membero(House(animal="snails", cigarettes="Old Gold"), houses),
    membero(House(color="yellow", cigarettes="Kools"), houses),
    eq(House(drink="milk"), houses[2]),
    eq(House("Norwegian"), houses[0]),
    nexto(House(cigarettes="Chesterfields"), House(animal="fox"), houses),
    nexto(House(cigarettes="Kools"), House(animal="horse"), houses),
    membero(House(drink="orange juice", cigarettes="Lucky Strike"), houses),
    membero(House("Japanese", cigarettes="Parliaments"), houses),
    nexto(House("Norwegian"), House(color="blue"), houses),
    membero(House(drink="water"), houses),
    membero(House(animal="zebra"), houses),
)


results = run(0, houses, goals)
print(results)
# (
#     [
#         House(
#             nationality="Norwegian",
#             drink="water",
#             animal="fox",
#             cigarettes="Kools",
#             color="yellow",
#         ),
#         House(
#             nationality="Ukrainian",
#             drink="tea",
#             animal="horse",
#             cigarettes="Chesterfields",
#             color="blue",
#         ),
#         House(
#             nationality="Englishman",
#             drink="milk",
#             animal="snails",
#             cigarettes="Old Gold",
#             color="red",
#         ),
#         House(
#             nationality="Spaniard",
#             drink="orange juice",
#             animal="dog",
#             cigarettes="Lucky Strike",
#             color="ivory",
#         ),
#         House(
#             nationality="Japanese",
#             drink="coffee",
#             animal="zebra",
#             cigarettes="Parliaments",
#             color="green",
#         ),
#     ],
# )
