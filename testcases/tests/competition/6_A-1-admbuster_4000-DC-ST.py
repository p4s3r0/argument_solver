
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/6_A-1-admbuster_4000.af")
s = AFSolver("ST", os.path.join(path, "6_A-1-admbuster_4000.af"))

for n in range(1, 4001):
	s.add_argument(n)

s.solve_cred([138])

s.del_attack(688, 689)
s.solve_cred([138])

s.del_attack(3746, 23)
s.solve_cred([138])

s.add_attack(3479, 1719)
s.solve_cred([138])

s.del_attack(3726, 3733)
s.solve_cred([138])

s.del_attack(883, 880)
s.solve_cred([138])

s.add_attack(3988, 3345)
s.solve_cred([138])

s.del_attack(1166, 1182)
s.solve_cred([138])

s.add_attack(1450, 7)
s.solve_cred([138])

