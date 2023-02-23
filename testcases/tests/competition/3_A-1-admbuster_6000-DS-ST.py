
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/3_A-1-admbuster_6000.af")
s = AFSolver("ST", os.path.join(path, "3_A-1-admbuster_6000.af"))

for n in range(1, 6001):
	s.add_argument(n)

s.solve_skept([123])

s.del_attack(321, 325)
s.solve_skept([123])

s.del_attack(5298, 5297)
s.solve_skept([123])

s.add_attack(3722, 3813)
s.solve_skept([123])

s.add_attack(4279, 4025)
s.solve_skept([123])

s.add_attack(4820, 2474)
s.solve_skept([123])

s.del_attack(4232, 4226)
s.solve_skept([123])

s.add_attack(2798, 5605)
s.solve_skept([123])

s.add_attack(829, 2276)
s.solve_skept([123])

