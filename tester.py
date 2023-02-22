from z3 import *

s = Solver()

one = Bool("1")
two = Bool("2")
thr = Bool("3")
fou = Bool("4")
fiv = Bool("5")

clause_1 = And(Implies(one,And(And(And(Not(two), Not(fiv)), Not(thr)),Not(fou))),one == And(And(And(fiv,Or(one, two)),two),Or(two, fiv)))
clause_2 = And(Implies(two, And(True, Not(fiv))), two == And(True, Or(Or(False, one), two)))
clause_3 = And(Implies(thr, And(True, Not(two))), thr == And(True, Or(False, fiv)))
clause_4 = And(Implies(fou, And(And(True, Not(two)), Not(fiv))), fou == And(And(True, Or(False, fiv)), Or(Or(False, one), two)))
clause_5 = And(Implies(fiv, And(And(True, Not(one)), Not(two))), fiv == And(And(True, Or(Or(Or(Or(False, two), fiv), thr), fou)), Or(False, fiv)))

s.add(clause_1)
s.add(clause_2)
s.add(clause_3)
s.add(clause_4)
s.add(clause_5)
s.add(fou == True)
if s.check() == sat:
    model = s.model()
    print(model)
else:
    print("NOT SAT")

