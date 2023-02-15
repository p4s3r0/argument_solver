import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/small/pims.af"))
s = AFSolver("CO", os.path.join(path, "pims.af"))

s.add_argument(6)
s.solve_skept([1, 5])