# `kanren`

[![Build Status](https://travis-ci.org/pythological/kanren.svg?branch=main)](https://travis-ci.org/pythological/kanren) [![Coverage Status](https://coveralls.io/repos/github/pythological/kanren/badge.svg?branch=main)](https://coveralls.io/github/pythological/kanren?branch=main) [![PyPI](https://img.shields.io/pypi/v/miniKanren)](https://pypi.org/project/miniKanren/) [![Join the chat at https://gitter.im/pythological/kanren](https://badges.gitter.im/pythological/kanren.svg)](https://gitter.im/pythological/kanren?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

Logic/relational programming in Python with [miniKanren](http://minikanren.org/).

## Installation

Using `pip`:
```bash
pip install miniKanren
```

Using `conda`:
```bash
conda install -c conda-forge miniKanren
```

## Development

First obtain the project source:
```bash
git clone git@github.com:pythological/kanren.git
cd kanren
```

Install the development dependencies:

```bash
$ pip install -r requirements.txt
```

Set up `pre-commit` hooks:

```bash
$ pre-commit install --install-hooks
```

Tests can be run with the provided `Makefile`:
```bash
make check
```

## Motivation

Logic programming is a general programming paradigm.  This implementation however came about specifically to serve as an algorithmic core for Computer Algebra Systems in Python and for the automated generation and optimization of numeric software.  Domain specific languages, code generation, and compilers have recently been a hot topic in the Scientific Python community.  `kanren` aims to be a low-level core for these projects.

These points&mdash;along with `kanren` examples&mdash;are covered in the paper ["miniKanren as a Tool for Symbolic Computation in Python"](https://arxiv.org/abs/2005.11644).

## Examples

`kanren` enables one to express sophisticated relations&mdash;in the form of *goals*&mdash;and generate values that satisfy the relations.  The following code is the "Hello, world!" of logic programming; it asks for values of the *logic variable* `x` such that `x == 5`:

```python
>>> from kanren import run, eq, membero, var, lall
>>> x = var()
>>> run(1, x, eq(x, 5))
(5,)
```

Multiple logic variables and goals can be used simultaneously.  The following code asks for one list containing the values of `x` and `z` such that `x == z` **and** `z == 3`:

```python
>>> z = var()
>>> run(1, [x, z], eq(x, z),
                   eq(z, 3))
([3, 3],)
```

`kanren` uses [unification](http://en.wikipedia.org/wiki/Unification_%28computer_science%29) to match forms within expression trees.  The following code asks for values of `x` such that `(1, 2) == (1, x)`:

```python
>>> run(1, x, eq((1, 2), (1, x)))
(2,)
```

The above examples use `eq`: a *goal constructor* that creates a goal for unification between two objects.  Other goal constructors, such as `membero(item, coll)`, express more sophisticated relations and are often constructed from simpler ones like `eq`.  More specifically, `membero` states that `item` is a member of the collection `coll`.

The following example uses `membero` to ask for *all* values of `x`, such that `x` is a member of `(1, 2, 3)` **and** `x` is a member of `(2, 3, 4)`.

```python
>>> run(0, x, membero(x, (1, 2, 3)),  # x is a member of (1, 2, 3)
              membero(x, (2, 3, 4)))  # x is a member of (2, 3, 4)
(2, 3)
```

The examples above made implicit use of the goal constructors `lall` and `lany`, which represent goal *conjunction* and *disjunction*, respectively.  Many useful relations can be expressed with `lall`, `lany`, and `eq` alone, but in `kanren` it's also easy to leverage the host language and explicitly create any relation expressible in Python.

### Representing Knowledge

`kanren` stores data as facts that state relationships between terms.  The following code creates a parent relationship and uses it to state facts about who is a parent of whom within the Simpsons family:

```python
>>> from kanren import Relation, facts
>>> parent = Relation()
>>> facts(parent, ("Homer", "Bart"),
...               ("Homer", "Lisa"),
...               ("Abe",  "Homer"))

>>> run(1, x, parent(x, "Bart"))
('Homer',)

>>> run(2, x, parent("Homer", x))
('Lisa', 'Bart')
```

We can use intermediate variables for more complex queries.  For instance, who is Bart's grandfather?

```python
>>> grandparent_lv, parent_lv = var(), var()
>>> run(1, grandparent_lv, parent(grandparent_lv, parent_lv),
                           parent(parent_lv, 'Bart'))
('Abe',)
```

We can express the grandfather relationship as a distinct relation by creating a goal constructor:
```python
>>> def grandparent(x, z):
...     y = var()
...     return lall(parent(x, y), parent(y, z))

>>> run(1, x, grandparent(x, 'Bart'))
('Abe,')
```

## Constraints

`kanren` provides a fully functional constraint system that allows one to restrict unification and object types:

```python
>>> from kanren.constraints import neq, isinstanceo

>>> run(0, x,
...     neq(x, 1),  # Not "equal" to 1
...     neq(x, 3),  # Not "equal" to 3
...     membero(x, (1, 2, 3)))
(2,)

>>> from numbers import Integral
>>> run(0, x,
...     isinstanceo(x, Integral),  # `x` must be of type `Integral`
...     membero(x, (1.1, 2, 3.2, 4)))
(2, 4)
```

## Graph Relations

`kanren` comes with support for relational graph operations suitable for basic symbolic algebra operations.  See the examples in [`doc/graphs.md`](doc/graphs.md).

## Extending `kanren`

`kanren` uses [`multipledispatch`](http://github.com/mrocklin/multipledispatch/) and the [`logical-unification` library](https://github.com/pythological/unification) to support pattern matching on user defined types.  Essentially, types that can be unified can be used with most `kanren` goals.  See the [`logical-unification` project's examples](https://github.com/pythological/unification#examples) for demonstrations of how arbitrary types can be made unifiable.

## About

This project is a fork of [`logpy`](https://github.com/logpy/logpy).

## References

* [Logic Programming on wikipedia](http://en.wikipedia.org/wiki/Logic_programming)
* [miniKanren](http://minikanren.org/), a Scheme library for relational programming on which this library is based.  More information can be found in the
[thesis of William
Byrd](https://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf).
