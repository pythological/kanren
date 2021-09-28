from operator import add, gt, sub

from examples.account import Account
from kanren import eq, membero, run, unifiable, var
from kanren.core import lall
from kanren.term import applyo, term  # noqa: F401

unifiable(Account)  # Register Account class

accounts = (
    Account("Adam", "Smith", 1, 20),
    Account("Carl", "Marx", 2, 3),
    Account("John", "Rockefeller", 3, 1000),
)

# optional name strings are helpful for debugging
first = var(prefix="first")
last = var(prefix="last")
ident = var(prefix="ident")
balance = var(prefix="balance")
newbalance = var(prefix="newbalance")

# Describe a couple of transformations on accounts
source = Account(first, last, ident, balance)
target = Account(first, last, ident, newbalance)

theorists = ("Adam", "Carl")
# Give $10 to theorists
theorist_bonus = lall(
    membero(source, accounts),
    membero(first, theorists),
    applyo(add, (10, balance), newbalance),
)

# Take $10 from anyone with more than $100
a = var(prefix="a")
tax_the_rich = lall(
    membero(source, accounts),
    applyo(gt, (balance, 100), a),
    eq(a, True),
    applyo(sub, (balance, 10), newbalance),
)

print("Take $10 from anyone with more than $100")
print(run(0, target, tax_the_rich))

print("Give $10 to theorists")
print(run(0, target, theorist_bonus))
