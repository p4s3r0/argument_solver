import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("../../argument_solver/inputs/small/pims.af"))
s = AFSolver("CO", os.path.join(path, "pims.af"))

s.solve_cred([])