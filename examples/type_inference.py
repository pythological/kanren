"""Relational typing for Python AST

Based on miniKanren examples provided by Jason Hemann.
"""
import ast
from collections.abc import Mapping
from numbers import Number
from typing import Callable, Dict, List, Tuple, _GenericAlias, _type_check

from cons import cons
from etuples import apply, rands, rator
from unification import reify, unify, var, vars
from unification.core import _reify, _unify, construction_sentinel
from unification.variable import Var

from kanren import conde, eq, lall, run
from kanren.constraints import isinstanceo, neq
from kanren.core import Zzz, fail
from kanren.goals import appendo, conso, nullo

rands.add((ast.AST,), lambda x: tuple(getattr(x, field) for field in x._fields))
rator.add((ast.AST,), lambda x: type(x))


def type_check(x):
    if isinstance(x, Var):
        return x
    else:
        return _type_check(x, f"{x} is not a type.")


def create_callable(inputs, outputs):
    """Create a ``Callable`` type that can contain logic variables."""
    inputs = tuple(type_check(i) for i in inputs)
    outputs = type_check(outputs)
    return _GenericAlias(
        Callable, inputs + (outputs,), inst=True, special=False, name="Callable"
    )


@_reify.register(ast.AST, Mapping)
def reify_AST(o, s):
    fields = [getattr(o, field, None) for field in o._fields]
    new_fields = yield _reify(fields, s)

    yield construction_sentinel

    if fields == new_fields:
        yield o
    else:
        yield type(o)(
            **{
                field_name: new_field
                for field_name, new_field in zip(o._fields, new_fields)
            }
        )


@_unify.register(ast.AST, ast.AST, Mapping)
def unify_AST(u, v, s):
    if type(u) != type(v):
        yield False
        return

    a = tuple(getattr(u, field, None) for field in u._fields)
    b = tuple(getattr(v, field, None) for field in v._fields)
    res = unify(a, b, s)

    yield res


@_reify.register(_GenericAlias, Mapping)
def reify_GenericAlias(o, s):
    """Reification for ``Callable[arg_types, out_types]``."""
    args = tuple(o.__args__)
    new_args = yield _reify(args, s)

    yield construction_sentinel

    if args == new_args:
        yield o
    else:
        if isinstance(o.__origin__, Callable):
            yield type(o)(
                o.__origin__,
                tuple(type_check(a) for a in new_args[:-1])
                + (type_check(new_args[-1]),),
                inst=o._inst,
                special=o._special,
                name=o._name,
            )
        else:
            yield type(o)(
                o.__origin__, new_args, inst=o._inst, special=o._special, name=o._name
            )


@_unify.register(_GenericAlias, _GenericAlias, Mapping)
def unify_GenericAlias(u, v, s):
    """Unification for ``Callable[arg_types, out_types]``."""
    if type(u) != type(v) or u.__origin__ != v.__origin__:
        yield False
        return

    a = tuple(u.__args__)
    b = tuple(v.__args__)
    res = unify(a, b, s)

    yield res


def lapplyo(relation, x, null_type=list, null_res=True, first=True):
    """Apply a relation to each element of an iterable."""
    y, r = var(), var()
    return conde(
        [nullo(x, default_ConsNull=null_type) if (not first or null_res) else fail],
        [
            conso(y, r, x),
            Zzz(relation, y),
            Zzz(lapplyo, relation, r, null_type=null_type, first=False),
        ],
    )


def absento(x, env):
    """Construct a relational goal asserting that `x` is not in `env`."""
    return lapplyo(lambda a: neq(x, a), env)


def turnstileo(x_env, t_env, e, t):
    """Relational operator for a typing relation.

    More specifically, `(!-o Γ e σ)` represents the statement
    "Γ ⊢ e: σ, where e is a term of type σ in context Γ".

    Use ``ast.dump(ast.parse("{1: 2}", mode="single").body[0])`` to obtain the
    ``ast`` expressions.

    Parameters
    ==========
    x_env:
        Type environment.
    t_env:
        Type environment.
    e:
        Expression to be typed.
    t:
        Type of `e`.

    """
    new_x_env_var, new_t_env_var = var(prefix="new_x_env"), var(prefix="new_t_env")
    nc_value_var = var()
    num_n_var = var()
    str_s_var = var()
    elts_var = var()
    keys_var, values_var = vars(2)
    fname_var, fargs_var, fbody_var = (
        var(prefix="fname"),
        var(prefix="fargs"),
        var(prefix="fbody"),
    )
    tx_var, tb_var = var(prefix="tx"), var(prefix="tb")
    rvalue_var = var()

    return conde(
        [
            # This is the generic "symbol" case
            eq(e, ast.Name(id=var(), ctx=var())),
            lookupo(x_env, t_env, e, t),
        ],
        [
            eq(e, ast.Return(value=rvalue_var)),
            Zzz(turnstileo, x_env, t_env, rvalue_var, t),
        ],
        [
            eq(e, ast.Num(n=num_n_var)),
            isinstanceo(num_n_var, Number),
            eq(int, t),
        ],
        [
            eq(e, ast.Str(s=str_s_var)),
            isinstanceo(str_s_var, str),
            eq(str, t),
        ],
        [
            eq(e, ast.NameConstant(value=nc_value_var)),
            conde([eq(nc_value_var, True)], [eq(nc_value_var, False)]),
            eq(bool, t),
        ],
        [
            eq(e, ast.List(elts=elts_var)),
            # TODO: Type each element.
            eq(List, t),
        ],
        [
            eq(e, ast.Tuple(elts=elts_var)),
            # TODO: Type each element.
            eq(Tuple, t),
        ],
        [
            eq(e, ast.Dict(keys=keys_var, values=values_var)),
            # TODO: Type each element.
            eq(Dict, t),
        ],
        [
            # A function definition
            eq(
                e,
                ast.FunctionDef(
                    name=fname_var,
                    args=ast.arguments(
                        args=fargs_var,
                        vararg=None,
                        kwonlyargs=[],
                        kw_defaults=[],
                        kwarg=None,
                        defaults=[],
                    ),
                    body=[fbody_var],
                    decorator_list=var(),
                    returns=var(),
                ),
            ),
            # The type of this statement is `Callable`
            eq(create_callable([tx_var], tb_var), t),
            # State that `fargs_var` must be an `ast.arg` type
            lapplyo(lambda x: eq(x, ast.arg(arg=var(), annotation=var())), fargs_var),
            #
            # Update the typing contexts
            #
            # Add every argument to the typing context
            appendo(fargs_var, x_env, new_x_env_var),
            # TODO: Handle multiple arguments and function body statements.
            # lapplyo(
            #     lambda x: tunstileo(new_x_env_var, new_y_env_var, x, var()), fargs_var
            # ),
            conso(cons("mono", tx_var), t_env, new_t_env_var),
            Zzz(
                turnstileo,
                new_x_env_var,
                new_t_env_var,
                fbody_var,
                tb_var,
            ),
        ]
        #
        # Conditional form:
        # If(test=Name(id='cond', ctx=Load()), body=[Pass()],
        # orelse=[If(test=Name(id='cond2', ctx=Load()), body=[Pass()],
        # orelse=[Pass()])])
        # [(fresh (te ce ae)
        #    (== `(if ,te ,ce ,ae) e)
        #    (absento 'if Γx)
        #    (⊢ Γx Γτ te '𝔹)
        #    (⊢ Γx Γτ ce τ)
        #    (⊢ Γx Γτ ae τ))]
        # [(fresh (x b τx τb)
        #    ;; we split the environment to facilitate shadow checking
        #    (absento 'lambda Γx)
        #    (symbolo x)
        #    (== `(lambda (,x) ,b) e)
        #    (== `(,τx → ,τb) τ)
        #    (⊢ `(,x . ,Γx) `((mono . ,τx) . ,Γτ) b τb))]
        #
        # Lambda definition:
        # Lambda(args=arguments(args=[arg(arg='x', annotation=None)],
        # vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[]),
        # body=BinOp(left=Num(n=1), op=Add(), right=Num(n=1)))
        #
        # Assignment:
        # Assign(targets=[Name(id='x', ctx=Store())], value=Name(id='y', ctx=Load()))
        # [(fresh (x e₁ b)
        #    (== `(let ((,x ,e₁)) ,b) e)
        #    (absento 'let Γx)
        #    (symbolo x)
        #    (⊢ `(,x . ,Γx) `((poly ,e₁ ,Γx ,Γτ) . ,Γτ) b τ))]
        #
        # (Unary) function application:
        # Expr(value=Call(func=Name(id='f', ctx=Load()), args=[Name(id='x',
        # ctx=Load())], keywords=[]))
        # [(fresh (e₁ e₂ τx)
        #    (== `(,e₁ ,e₂) e)
        #    (⊢ Γx Γτ e₁ `(,τx → ,τ))
        #    (⊢ Γx Γτ e₂ τx))]
        #     [(fresh [e1 e2]
        #
        # Addition function:
        # Expr(value=BinOp(left=Num(n=1), op=Add(), right=Num(n=1)))
        # [(fresh (ne₁ ne₂)
        #    (== `(+ ,ne₁ ,ne₂) e)
        #    (absento '+ Γx)
        #    (== 'ℕ τ)
        #    (⊢ Γx Γτ ne₁ 'ℕ)
        #    (⊢ Γx Γτ ne₂ 'ℕ))]
    )


def lookupo(x_env, t_env, x, t):
    x_env_, t_env_, y, m_p, res = vars(5)
    et, x_env__, t_env__ = vars(3)

    return lall(
        conso(y, x_env_, x_env),
        conso(cons(m_p, res), t_env_, t_env),
        conde(
            [
                eq(x, y),
                conde(
                    [eq(m_p, "mono"), eq(res, t)],
                    [
                        eq(m_p, "poly"),
                        eq(res, [et, x_env__, t_env__]),
                        Zzz(turnstileo, x_env__, t_env__, et, t),
                    ],
                ),
            ],
            [neq(x, y), Zzz(lookupo, x_env_, t_env_, x, t)],
        ),
    )


def test_etuples_ast():
    expr = ast.parse("return 1 + 1", mode="single").body[0]
    expr2 = apply(rator(expr), rands(expr))

    assert type(expr) == type(expr2)
    assert all(getattr(expr, field) == getattr(expr, field) for field in expr._fields)


def test_unify_reify_ast():
    a_var = var()
    b_var = var()

    expr = ast.Name(id="blah", ctx=ast.Load())
    template_expr = ast.Name(id=b_var, ctx=a_var)
    s = unify(template_expr, expr, {})

    assert s[b_var] == expr.id
    assert s[a_var] == expr.ctx

    reified_expr = reify(template_expr, s)
    assert reified_expr.id is expr.id
    assert reified_expr.ctx is expr.ctx

    assert unify(ast.Name(id="blah", ctx=a_var), expr, {})
    assert unify(ast.Name(id="blah1", ctx=a_var), expr, {}) is False

    expr = ast.NameConstant(value="blah")
    s = unify(ast.NameConstant(value=a_var), expr, {})

    assert s[a_var] == expr.value

    expr = ast.Num(n=1)
    s = unify(ast.Num(n=a_var), expr, {})

    assert s[a_var] == expr.n


def test_unify_reify_types():

    a_var = var()
    b_var = var()

    test_callable = create_callable([int, str], list)
    template_callable = create_callable([a_var, str], b_var)

    s = unify(test_callable, template_callable)
    assert s[a_var] == int
    assert s[b_var] == list

    res = reify(template_callable, s)
    assert test_callable == res

    test_callable = create_callable([int, tuple], list)
    assert unify(test_callable, template_callable) is False


# TODO: Might want to use the pytest timeout plugin and
# `pytest.mark.timeout(30, method='thread')`.
def test_turnstileo():
    expr_var = var(prefix="expr")
    type_var = var(prefix="type")
    x_env_var = var(prefix="x_env")
    t_env_var = var(prefix="t_env")

    res = run(
        1,
        (x_env_var, t_env_var, expr_var),
        turnstileo(x_env_var, t_env_var, expr_var, int),
    )

    assert isinstance(res[0][2], ast.Name)

    num_1 = ast.Num(n=1)
    res = run(0, type_var, turnstileo([], [], num_1, type_var))
    assert res == (int,)

    num_1 = ast.Num(n="a")
    assert run(0, type_var, turnstileo([], [], num_1, type_var)) == ()

    symbol_1 = ast.Name(id="a", ctx=ast.Load())
    res = run(0, type_var, turnstileo([], [], symbol_1, type_var))
    assert res == ()

    expr = ast.parse("def func(x):\n\treturn 1", mode="single").body[0]
    # import astor; print(astor.dump_tree(expr))

    res = run(
        0,
        type_var,
        turnstileo([], [], expr, type_var),
    )

    assert isinstance(res[0], Callable)
    assert res[0].__args__[-1] == int
