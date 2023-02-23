
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/4_B-1-BA_40_30_3.af")
s = AFSolver("ST", os.path.join(path, "4_B-1-BA_40_30_3.af"))

for n in range(1, 42):
	s.add_argument(n)

s.solve_skept([37])

s.add_attack(12, 30)
s.solve_skept([37])

s.add_attack(28, 7)
s.solve_skept([37])

s.add_attack(13, 4)
s.solve_skept([37])

s.del_attack(33, 39)
s.solve_skept([37])

s.del_attack(13, 35)
s.solve_skept([37])

s.add_attack(29, 23)
s.solve_skept([37])

s.del_attack(30, 25)
s.solve_skept([37])

s.del_attack(20, 27)
s.solve_skept([37])

