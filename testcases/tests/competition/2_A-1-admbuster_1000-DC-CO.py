
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/2_A-1-admbuster_1000.af")
s = AFSolver("CO", os.path.join(path, "2_A-1-admbuster_1000.af"))

for n in range(1, 1001):
	s.add_argument(n)

s.solve_cred([112])

s.add_attack(109, 102)
s.solve_cred([112])

s.add_attack(421, 165)
s.solve_cred([112])

s.add_attack(797, 457)
s.solve_cred([112])

s.del_attack(700, 689)
s.solve_cred([112])

s.del_attack(357, 370)
s.solve_cred([112])

s.del_attack(238, 243)
s.solve_cred([112])

s.add_attack(42, 510)
s.solve_cred([112])

s.del_attack(586, 51)
s.solve_cred([112])

