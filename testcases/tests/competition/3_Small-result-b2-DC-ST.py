
import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname("../../argument_solver/inputs/competition/Small-result-b2.af")
s = AFSolver("ST", os.path.join(path, "Small-result-b2.af"))

s.del_attack(1, 2)
s.del_attack(4, 2)
s.add_attack(2, 3)
s.add_attack(3, 1)
s.del_attack(4, 5)
s.add_attack(2, 5)
s.add_attack(4, 1)
s.add_attack(5, 2)

for n in range(1, 6):
	s.add_argument(n)

s.solve_cred([4])