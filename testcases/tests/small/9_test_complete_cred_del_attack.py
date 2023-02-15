import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/small/pims_one_toomuch.af"))
s = AFSolver("CO", os.path.join(path, "pims_one_toomuch.af"))

s.del_attack(2, 1)
s.solve_cred([])
s.printSolution()