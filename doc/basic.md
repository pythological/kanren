# Basics of `miniKanren`

The design of `miniKanren` is simple.  It orchestrates only a few basic operations and yields a lot!

## Terms

Terms can be

- any Python object (e.g. `1`, `[1, 2]`, `object()`, etc.),
- logical variables constructed with `var`&mdash;denoted here by a tilde prefix (e.g. `~x`),
- or combinations of the two (e.g. `(1, ~x, 'cat')`)

In short, they are trees in which leaves may be either constants or variables.  Constants may be of any Python type.

## Unification

We *unify* two similar terms like `(1, 2)` and `(1, ~x)` to form a *substitution* `{~x: 2}`.  We say that `(1, 2)` and `(1, ~x)` unify under the substitution `{~x: 2}`.  Variables may assume the value of any term.

`unify` is a function, provided by the [`logical-unification`](https://github.com/pythological/unification) library, that takes two terms, `u` and `v`, and returns a substitution `s`.

Examples that unify

|       u           |       v           |        s          |
|:-----------------:|:-----------------:|:-----------------:|
| 123               | 123               | {}                |
| 'cat'             | 'cat'             | {}                |
| (1, 2)            | (1, 2)            | {}                |
| ~x                | 1                 | {~x: 1}           |
| 1                 | ~x                | {~x: 1}           |
| (1, ~x)           | (1, 2)            | {~x: 2}           |
| (1, 1)            | (~x, ~x)          | {~x: 1}           |
| (1, 2, ~x)        | (~y, 2, 3)        | {~x: 3, ~y: 1}    |

Examples that don't unify

|       u           |       v           |
|:-----------------:|:-----------------:|
| 123               | 'cat'             |
| (1, 2)            | 12                |
| (1, ~x)           | (2, 2)            |
| (1, 2)            | (~x, ~x)          |

Actually we lied, `unify` also takes a substitution as input.  This allows us to keep some history around.  For example:

```python
>>> unify((1, 2), (1, x), {})  # normal case
{~x: 2}
>>> unify((1, 2), (1, x), {x: 2})  # x is already two. This is consitent
{~x: 2}
>>> unify((1, 2), (1, x), {x: 3})  # x is already three.  This conflicts
False
```

## Reification

Reification is the opposite of unification.  `reify` transforms a term with logic variables like `(1, ~x)` and a substitution like `{~x: 2}` into a term without logic variables like `(1, 2)`.
```python
>>> reify((1, x), {x: 2})
(1, 2)
```

## Goals and Goal Constructors

A *goal* is a function from one substitution to a stream of substitutions.

```
goal :: substitution -> [substitutions]
```

We make goals with a *goal constructors*.  Goal constructors are the normal building block of a logical program.  Lets look at the goal constructor `membero` which states that the first input must be a member of the second input (a collection).

```
goal = membero(x, (1, 2, 3)
```

We can feed this goal a substitution and it will give us a stream of substitutions.  Here we'll feed it the substitution with no information and it will tell us that either `x` can be `1` or `x` can be `2` or `x` can be `3`

```python
>>> for s in goal({}):
...     print s
{~x: 1}
{~x: 2}
{~x: 3}
```
What if we already know that `x` is `2`?
```python
>>> for s in goal({x: 2}):
...     print s
{~x: 2}
```

Remember *goals* are functions from one substitution to a stream of substitutions.  Users usually make goals with *goal constructors* like `eq`, or `membero`.

### Stream Functions

After this point `miniKanren` is just a library to manage streams of substitutions.

For example if we know both that `membero(x, (1, 2, 3))` and `membero(x, (2, 3, 4))` then we could do something like the following:

```python
>>> g1 = membero(x, (1, 2, 3))
>>> g2 = membero(x, (2, 3, 4))
>>> for s in g1({}):
...     for ss in g2(s):
...         print ss
{~x: 2}
{~x: 3}
```
Logic programs can have many goals in complex hierarchies.  Writing explicit for loops would quickly become tedious.  Instead `miniKanren` provide functions that perform logic-like operations on goal streams.

```
combinator :: [goals] -> goal
```

Two important stream functions are logical all `lall` and logical any `lany`.
```python
>>> g = lall(g1, g2)
>>> for s in g({}):
...     print s
{~x: 2}
{~x: 3}

>>> g = lany(g1, g2)
>>> for s in g({}):
...     print s
{~x: 1}
{~x: 2}
{~x: 3}
{~x: 4}
```

### Laziness

Goals produce a stream of substitutions.  This stream is computed lazily, returning values only as they are needed.  `miniKanren` depends on standard Python generators to maintain the necessary state and control flow.

```python
>>> stream = g({})
>>> stream
<generator object unique at 0x2e13690>
>>> next(stream)
{~x: 1}
```

## User Interface

Traditionally programs are run with the `run` function

```python
>>> x = var()
>>> run(0, x, membero(x, (1, 2, 3)), membero(x, (2, 3, 4)))
(2, 3)
```
`run` has an implicit `lall` for the goals at the end of the call.  It `reifies` results when it returns so that the user never has to touch logic variables or substitutions.

## Conclusion

These are all the fundamental concepts that exist in `miniKanren`.  To summarize:

- *Term*: a Python object, logic variable, or combination of the two
- *Substitution Map*: a dictionary mapping logic variables to terms
- *Unification*: A function that finds logic variable substitutions that make two terms equal
- *Reification*: A function that substitutes logic variables in a term with values given by a substitution map
- *Goal*: A generator function that takes a substitution and yields a stream of substitutions
- *Goal Constructor*: A user-level function that constructs and returns a goal
