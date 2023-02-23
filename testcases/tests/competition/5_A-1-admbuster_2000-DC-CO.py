
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/5_A-1-admbuster_2000.af")
s = AFSolver("CO", os.path.join(path, "5_A-1-admbuster_2000.af"))

for n in range(1, 2001):
	s.add_argument(n)

s.solve_cred([116])

s.add_attack(718, 924)
s.solve_cred([116])

s.del_attack(1462, 1960)
s.solve_cred([116])

s.add_attack(380, 1469)
s.solve_cred([116])

s.add_attack(1504, 1627)
s.solve_cred([116])

s.add_attack(725, 810)
s.solve_cred([116])

s.add_attack(438, 1257)
s.solve_cred([116])

s.del_attack(450, 445)
s.solve_cred([116])

s.del_attack(371, 1836)
s.solve_cred([116])

