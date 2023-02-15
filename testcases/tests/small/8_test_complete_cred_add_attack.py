import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/small/pims_missing_one.af"))
s = AFSolver("CO", os.path.join(path, "pims_missing_one.af"))

s.add_argument(1)
s.add_attack(1, 2)
s.solve_cred([])
s.printSolution()