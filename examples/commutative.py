from kanren import fact, run, var
from kanren.assoccomm import associative, commutative
from kanren.assoccomm import eq_assoccomm as eq

# Define some dummy Operationss
add = "add"
mul = "mul"

# Declare that these ops are commutative using the facts system
fact(commutative, mul)
fact(commutative, add)
fact(associative, mul)
fact(associative, add)

# Define some logic variables
x, y = var(), var()

# Two expressions to match
pattern = (mul, (add, 1, x), y)  # (1 + x) * y
expr = (mul, 2, (add, 3, 1))  # 2 * (3 + 1)

res = run(0, (x, y), eq(pattern, expr))
print(res)
# prints ((3, 2),) meaning
#   x matches to 3
#   y matches to 2
