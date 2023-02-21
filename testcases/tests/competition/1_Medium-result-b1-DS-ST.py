
import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname("../../argument_solver/inputs/competition/Medium-result-b1.af")
s = AFSolver("ST", os.path.join(path, "Medium-result-b1.af"))

s.del_attack(96, 434)
s.add_attack(139, 32)
s.del_attack(225, 358)
s.del_attack(409, 31)
s.add_attack(288, 300)
s.del_attack(86, 33)
s.add_attack(33, 346)
s.del_attack(294, 420)

s.solve_skept([262])