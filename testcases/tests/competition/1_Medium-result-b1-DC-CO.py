import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/competition/Medium-result-b1.af"))
s = AFSolver("DC", os.path.join(path, "Medium-result-b1.af"))

s.solve_cred([262])