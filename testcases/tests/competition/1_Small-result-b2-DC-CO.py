
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/1_Small-result-b2.af")
s = AFSolver("CO", os.path.join(path, "1_Small-result-b2.af"))

for n in range(1, 6):
	s.add_argument(n)

s.solve_cred([4])

s.del_attack(1, 2)
s.solve_cred([4])

s.del_attack(4, 2)
s.solve_cred([4])

s.add_attack(2, 3)
s.solve_cred([4])

s.add_attack(3, 1)
s.solve_cred([4])

s.del_attack(4, 5)
s.solve_cred([4])

s.add_attack(2, 5)
s.solve_cred([4])

s.add_attack(4, 1)
s.solve_cred([4])

s.add_attack(5, 2)
s.solve_cred([4])

