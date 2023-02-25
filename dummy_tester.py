# -----------------------------------------------------------------------------
# DUMMY_TESTER.PY
# Used to run some dummy tests.
# -----------------------------------------------------------------------------
from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("inputs/small/pims.af"))
s = AFSolver("CO", os.path.join(path, "pims.af"))

s.solve_cred([])
s.solve_cred([1])