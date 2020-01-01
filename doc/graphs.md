# Relational Graph Manipulation

In this document, we show how `kanren` can be used to perform symbolic algebra operations *relationally*.

## Setup

First, we import the necessary modules and create a helper function for pretty printing the algebraic expressions.

```python
from math import log, exp
from numbers import Real
from functools import partial
from operator import add, mul

from unification import var

from etuples.core import etuple, ExpressionTuple

from kanren import run, eq, conde, lall
from kanren.core import success
from kanren.graph import walko, reduceo
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

Next, we create a simple goal constructor that implements the algebraic relations `x + x == 2 * x` and `log(exp(x)) == x` and
constrains the input types to real numbers and expression tuples from the [`etuples`](https://github.com/pythological/etuples) package.

```python
def single_math_reduceo(expanded_term, reduced_term):
    """Construct a goal for some simple math reductions."""
    # Create a logic variable to represent our variable term "x"
    x_lv = var()
    # `conde` is a relational version of Lisp's `cond`/if-else; here, each
    # "branch" pairs the right- and left-hand sides of a replacement rule with
    # the corresponding inputs.
    return lall(
        isinstanceo(x_lv, Real),
        isinstanceo(x_lv, ExpressionTuple),
        conde(
            # add(x, x) == mul(2, x)
            [eq(expanded_term, etuple(add, x_lv, x_lv)),
             eq(reduced_term, etuple(mul, 2, x_lv))],
            # log(exp(x)) == x
            [eq(expanded_term, etuple(log, etuple(exp, x_lv))),
             eq(reduced_term, x_lv)]),
    )

```

In order to obtain "fully reduced" results, we need to turn `math_reduceo` into a fixed-point-producing relation (i.e. recursive).
```python
math_reduceo = partial(reduceo, single_math_reduceo)
```

We also need a relation that walks term graphs specifically (i.e. graphs composed of operator and operand combinations) and necessarily produces its output in the form of expression tuples.
```python
term_walko = partial(walko, rator_goal=eq, null_type=ExpressionTuple)
```

## Reductions

The following example is a straight-forward reduction&mdash;i.e. left-to-right applications of the relations in `math_reduceo`&mdash;of the term `add(etuple(add, 3, 3), exp(log(exp(5))))`.  This is the direction in which results are normally computed in symbolic algebra libraries.

```python
# This is the term we want to reduce
expanded_term = etuple(add, etuple(add, 3, 3), etuple(exp, etuple(log, etuple(exp, 5))))

# Create a logic variable to represent the results we want to compute
reduced_term = var()

# Asking for 0 results means all results
res = run(3, reduced_term, term_walko(math_reduceo, expanded_term, reduced_term))
```

```python
>>> print('\n'.join((f'{expanded_term} == {r}' for r in res)))
add(add(3, 3), exp(log(exp(5)))) == add(mul(2, 3), exp(5))
add(add(3, 3), exp(log(exp(5)))) == add(add(3, 3), exp(5))
add(add(3, 3), exp(log(exp(5)))) == add(mul(2, 3), exp(log(exp(5))))
```

## Expansions

In this example, we're specifying a grounded reduced term (i.e. `mul(2, 5)`) and an unground expanded term (i.e. the logic variable `q_lv`).  We're essentially asking for *graphs that would reduce to `mul(2, 5)`*.  Naturally, there are infinitely many graphs that reduce to `mul(2, 5)`, so we're only going to ask for ten of them; nevertheless, miniKanren is inherently capable of handling infinitely many results through its use of lazily evaluated goal streams.

```python
expanded_term = var()
reduced_term = etuple(mul, 2, 5)

# Ask for 10 results of `q_lv`
res = run(10, expanded_term, term_walko(math_reduceo, expanded_term, reduced_term))
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
Now, we set **both** term graphs to unground logic variables.

```python
expanded_term = var()
reduced_term = var()

res = run(10, [expanded_term, reduced_term],
          term_walko(math_reduceo, expanded_term, reduced_term))
```

```python
>>> rjust = max(map(lambda x: len(str(x[0])), res))
>>> print('\n'.join((f'{str(e):>{rjust}} == {str(r)}' for e, r in res)))
                                        add(~_2291, ~_2291) == mul(2, ~_2291)
                                                   ~_2288() == ~_2288()
                              log(exp(add(~_2297, ~_2297))) == mul(2, ~_2297)
                                ~_2288(add(~_2303, ~_2303)) == ~_2288(mul(2, ~_2303))
                    log(exp(log(exp(add(~_2309, ~_2309))))) == mul(2, ~_2309)
                                             ~_2288(~_2294) == ~_2288(~_2294)
          log(exp(log(exp(log(exp(add(~_2315, ~_2315))))))) == mul(2, ~_2315)
                                           ~_2288(~_2300()) == ~_2288(~_2300())
log(exp(log(exp(log(exp(log(exp(add(~_2325, ~_2325))))))))) == mul(2, ~_2325)
                        ~_2288(~_2294, add(~_2331, ~_2331)) == ~_2288(~_2294, mul(2, ~_2331))
```

The symbols prefixed by `~` are the string form of logic variables, so a result like `add(~_2291, ~_2291)` essentially means `add(x, x)` for some variable `x`.  In this instance, miniKanren has used our algebraic relations in `math_reduceo` to produce more relations&mdash;even some with variable operators with multiple arities!

With additional goals, we can narrow-in on very specific types of expressions.  In the following, we state that `expanded_term` must be the [`cons`](https://github.com/pythological/python-cons) of a `log` and logic variable (i.e. anything else).  In other words, we're stating that the operator of `expanded_term` must be a `log`, or that we want all expressions expanding to a `log`.

```python
from kanren.goals import conso

res = run(10, [expanded_term, reduced_term],
          conso(log, var(), expanded_term),
          term_walko(math_reduceo, expanded_term, reduced_term))
```
```python
>>> rjust = max(map(lambda x: len(str(x[0])), res))
>>> print('\n'.join((f'{str(e):>{rjust}} == {str(r)}' for e, r in res)))
                              log(exp(add(~_2344, ~_2344))) == mul(2, ~_2344)
                                                      log() == log()
                                    log(exp(~reduced_2285)) == ~reduced_2285
                                   log(add(~_2354, ~_2354)) == log(mul(2, ~_2354))
                    log(exp(log(exp(add(~_2360, ~_2360))))) == mul(2, ~_2360)
                                                log(~_2347) == log(~_2347)
          log(exp(log(exp(log(exp(add(~_2366, ~_2366))))))) == mul(2, ~_2366)
                                              log(~_2351()) == log(~_2351())
log(exp(log(exp(log(exp(log(exp(add(~_2376, ~_2376))))))))) == mul(2, ~_2376)
                           log(~_2347, add(~_2382, ~_2382)) == log(~_2347, mul(2, ~_2382))
```

The output contains a nullary `log` function, which isn't a valid expression.  We can restrict this type of output by further stating that the `log` expression's `cdr` term is itself the result of a `cons` and, thus, not an empty sequence.

```python
exp_term_cdr = var()

res = run(10, [expanded_term, reduced_term],
          conso(log, exp_term_cdr, expanded_term),
          conso(var(), var(), exp_term_cdr),
          term_walko(math_reduceo, expanded_term, reduced_term))
```
```python
>>> rjust = max(map(lambda x: len(str(x[0])), res))
>>> print('\n'.join((f'{str(e):>{rjust}} == {str(r)}' for e, r in res)))
                              log(exp(add(~_2457, ~_2457))) == mul(2, ~_2457)
                                   log(add(~_2467, ~_2467)) == log(mul(2, ~_2467))
                                           log(exp(~_2446)) == ~_2446
                                                log(~_2460) == log(~_2460)
                    log(exp(log(exp(add(~_2477, ~_2477))))) == mul(2, ~_2477)
                                              log(~_2464()) == log(~_2464())
          log(exp(log(exp(log(exp(add(~_2487, ~_2487))))))) == mul(2, ~_2487)
                           log(~_2460, add(~_2493, ~_2493)) == log(~_2460, mul(2, ~_2493))
log(exp(log(exp(log(exp(log(exp(add(~_2499, ~_2499))))))))) == mul(2, ~_2499)
                         log(log(exp(add(~_2501, ~_2501)))) == log(mul(2, ~_2501))
```
