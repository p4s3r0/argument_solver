import sys
from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("inputs/small/tester.af"))
s = AFSolver("CO", os.path.join(path, "tester.af"))

s.solve_cred([])
s.printSolution()