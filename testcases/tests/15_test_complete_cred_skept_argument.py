import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/pims.af"))
s = AFSolver("CO", os.path.join(path, "pims.af"))

s.add_argument(6)
s.solve_cred([])
s.printSolution()

