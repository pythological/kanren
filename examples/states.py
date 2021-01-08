"""
An example showing how to use facts and relations to store data and query data

This example builds a small database of the US states.

The `adjacency` relation expresses which states border each other.
The `coastal` relation expresses which states border the ocean.
"""
from kanren import Relation, fact, run, var

adjacent = Relation()
coastal = Relation()


coastal_states = (
    "WA,OR,CA,TX,LA,MS,AL,GA,FL,SC,NC,VA,MD,DE,NJ,NY,CT,RI,MA,ME,NH,AK,HI".split(",")
)

# ['NY', 'NJ', 'CT', ...]
for state in coastal_states:
    # E.g. 'NY' is coastal
    fact(coastal, state)

# Lines like 'CA,OR,NV,AZ'
with open("examples/data/adjacent-states.txt") as f:
    adjlist = [line.strip().split(",") for line in f if line and line[0].isalpha()]

# ['CA', 'OR', 'NV', 'AZ']
for L in adjlist:
    # 'CA', ['OR', 'NV', 'AZ']
    head, tail = L[0], L[1:]
    for state in tail:
        # E.g. 'CA' is adjacent to 'OR', 'CA' is adjacent to 'NV', etc.
        fact(adjacent, head, state)

x = var()
y = var()

# Is California adjacent to New York?
print(run(0, x, adjacent("CA", "NY")))
# ()

# All states next to California
print(run(0, x, adjacent("CA", x)))
# ('AZ', 'OR', 'NV')

# All coastal states next to Texas
print(run(0, x, adjacent("TX", x), coastal(x)))
# ('LA',)

# Five states that border a coastal state
print(run(5, x, coastal(y), adjacent(x, y)))
# ('LA', 'NM', 'OK', 'AR', 'RI')

# All states adjacent to Tennessee and adjacent to Florida
print(run(0, x, adjacent("TN", x), adjacent("FL", x)))
# ('AL', 'GA')
