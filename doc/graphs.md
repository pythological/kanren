# Relational Graph Manipulation

In this document, we show how `kanren` can be used to perform symbolic algebra graph reductions, expansions, and combinations of the two.

## Setup

First, we import the necessary modules and create a helper function for pretty printing the algebraic expressions:

```python
from math import log, exp
from numbers import Real
from functools import partial
from operator import add, mul

from unification import var

from etuples.core import etuple, ExpressionTuple

from kanren import run, eq, conde, lall
from kanren.graph import graph_applyo, reduceo
from kanren.constraints import isinstanceo


# Just some nice formatting
def etuple_str(self):
    if len(self) > 0:
        return f"{getattr(self[0], '__name__', self[0])}({', '.join(map(str, self[1:]))})"
    else:
        return 'noop'

ExpressionTuple.__str__ = etuple_str
del ExpressionTuple._repr_pretty_

```


Next, we create a simple goal constructor that implements the relations `x + x == 2 * x` and `log(exp(x)) == x`:

```python
def math_reduceo(expanded_term, reduced_term):
    """Construct a goal for some simple math reductions."""
    # Create a logic variable to represent our variable term "x"
    x_lv = var()
    # `conde` is a relational version of Lisp's `cond`/if-else; here, each
    # "branch" pairs the right- and left-hand sides of a replacement rule with
    # the corresponding inputs.
    return lall(conde(
                    # add(x, x) == mul(2, x)
                    [eq(expanded_term, etuple(add, x_lv, x_lv)),
                     eq(reduced_term, etuple(mul, 2, x_lv))],
                    # log(exp(x)) == x
                    [eq(expanded_term, etuple(log, etuple(exp, x_lv))),
                     eq(reduced_term, x_lv)]),
                conde([isinstanceo(x_lv, Real)],
                      [isinstanceo(x_lv, ExpressionTuple)]))


# Make `math_reduceo` recursive
fp_math_reduceo = partial(reduceo, math_reduceo)
```

## Reductions

The following example is a straight-forward reduction&mdash;i.e. left-to-right applications of the relations in `math_reduceo`&mdash;of the term `add(etuple(add, 3, 3), exp(log(exp(5))))`:

```python
# This is the term we want to reduce
expanded_term = etuple(add, etuple(add, 3, 3), etuple(exp, etuple(log, etuple(exp, 5))))

# Create a logic variable to represent the results we want to compute
reduced_term = var()

# Asking for 0 results means all results
res = run(0, reduced_term, graph_applyo(fp_math_reduceo, expanded_term, reduced_term))
```

```python
>>> print('\n'.join((f'{expanded_term} == {r}' for r in res)))
add(add(3, 3), exp(log(exp(5)))) == add(mul(2, 3), exp(5))
add(add(3, 3), exp(log(exp(5)))) == add(add(3, 3), exp(5))
add(add(3, 3), exp(log(exp(5)))) == add(mul(2, 3), exp(log(exp(5))))
```

## Expansions
In this example, we're specifying a "concrete" reduced term (i.e. `mul(2, 5)`) and an "unknown" expanded term (i.e. the logic variable `q_lv`).  We're essentially asking for graphs that would reduce to `mul(2, 5)`.
```python
expanded_term = var()
reduced_term = etuple(mul, 2, 5)

# Ask for 10 results of `q_lv`
res = run(10, expanded_term, graph_applyo(math_reduceo, expanded_term, reduced_term))
```
```python
>>> rjust = max(map(lambda x: len(str(x)), res))
>>> print('\n'.join((f'{str(r):>{rjust}} == {reduced_term}' for r in res)))
                                        add(5, 5) == mul(2, 5)
                    mul(log(exp(2)), log(exp(5))) == mul(2, 5)
                              log(exp(add(5, 5))) == mul(2, 5)
                              mul(2, log(exp(5))) == mul(2, 5)
                    log(exp(log(exp(add(5, 5))))) == mul(2, 5)
          mul(log(exp(log(exp(2)))), log(exp(5))) == mul(2, 5)
          log(exp(log(exp(log(exp(add(5, 5))))))) == mul(2, 5)
                    mul(2, log(exp(log(exp(5))))) == mul(2, 5)
log(exp(log(exp(log(exp(log(exp(add(5, 5))))))))) == mul(2, 5)
mul(log(exp(log(exp(log(exp(2)))))), log(exp(5))) == mul(2, 5)
```

## Expansions _and_ Reductions
Now, we set both terms to "unknowns".
```python
expanded_term = var()
reduced_term = var('r')

res = run(10, [expanded_term, reduced_term],
          graph_applyo(math_reduceo, expanded_term, reduced_term))
```

```python
>>> rjust = max(map(lambda x: len(str(x[0])), res))
>>> print('\n'.join((f'{str(e):>{rjust}} == {str(r)}' for e, r in res)))
                     add(~_3289, ~_3289) == mul(2, ~_3289)
           log(exp(add(~_3293, ~_3293))) == mul(2, ~_3293)
                                    noop == noop
add(mul(2, ~_3320), add(~_3320, ~_3320)) == mul(2, mul(2, ~_3320))
                        log(exp(~_3289)) == ~_3289
 log(exp(log(exp(add(~_3328, ~_3328))))) == mul(2, ~_3328)
                                ~_3297() == ~_3297()
 log(log(exp(exp(add(~_3338, ~_3338))))) == mul(2, ~_3338)
                          log(exp(noop)) == noop
                          ~_3297(~_3333) == ~_3297(~_3333)
```
The symbols prefixed by `~` are logic variables, so a result like `add(~_3289, ~3289)` basically means `add(x, x)` for some variable `x`.
