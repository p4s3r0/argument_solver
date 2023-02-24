# -----------------------------------------------------------------------------
# DUMMY_TESTER.PY
# Used to run some dummy tests.
# -----------------------------------------------------------------------------
from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("inputs/small/tester.af"))
s = AFSolver("CO", os.path.join(path, "tester.af"))

s.add_argument(9)
s.del_argument(9)
s.del_argument(9)