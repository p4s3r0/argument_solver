
import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname("../../argument_solver/inputs/competition/Medium-result-b1.af")
s = AFSolver("CO", os.path.join(path, "Medium-result-b1.af"))

s.del_attack(178, 268)
s.add_attack(245, 54)
s.del_attack(423, 198)
s.del_attack(250, 53)
s.add_attack(260, 292)
s.del_attack(160, 55)
s.add_attack(55, 68)
s.del_attack(266, 383)

for n in range(1, 439):
	s.add_argument(n)

s.solve_skept([132])