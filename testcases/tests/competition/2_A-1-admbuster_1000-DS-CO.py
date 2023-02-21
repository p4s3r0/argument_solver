
import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname("../../argument_solver/inputs/competition/A-1-admbuster_1000.af")
s = AFSolver("CO", os.path.join(path, "A-1-admbuster_1000.af"))

s.add_attack(477, 449)
s.add_attack(302, 689)
s.add_attack(590, 183)
s.del_attack(821, 816)
s.del_attack(814, 952)
s.del_attack(636, 308)
s.add_attack(776, 171)
s.del_attack(274, 877)

s.solve_skept([448])