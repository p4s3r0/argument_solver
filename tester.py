from z3 import *


z3_all_nodes = dict()
a = z3.Bool("a")
z3_all_nodes["a"] = a
b = z3.Bool("b")
z3_all_nodes["b"] = b
c = z3.Bool("c")
z3_all_nodes["c"] = c
d = z3.Bool("d")
z3_all_nodes["d"] = d
e = z3.Bool("e")
z3_all_nodes["e"] = e

s = z3.Solver()

fa = Implies(a, True)
fb = And(Implies(b, And(And(True, Not(a)), Not(c))),
    Implies(b, And(And(True, False), Or(False, d))))
fc = And(Implies(c, And(True, Not(d))),
    Implies(c, And(True, Or(False, c))))
fd = And(Implies(d, And(True, Not(c))),
    Implies(d, And(True, Or(False, d))))
fe = And(Implies(e, And(And(True, Not(d)), Not(e))),
    Implies(e,
            And(And(True, Or(False, c)),
                Or(Or(False, d), e))))

s.add(fa)
s.add(fb)
s.add(fc)
s.add(fd)
s.add(fe)





def negatePreviousModel(model: z3.Model):
    negate_prev_model = False
    for m in model:
        negate_prev_model = z3.Or(z3_all_nodes[str(m)] != model[m], negate_prev_model)
    s.add(negate_prev_model)



while s.check() == z3.sat:
    model = s.model()
    print(model)
    negatePreviousModel(model)

