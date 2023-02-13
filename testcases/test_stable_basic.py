from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/pims.af"))
s = AFSolver("ST", os.path.join(path, "pims.af"))
s.solve_cred([0])
s.printSolution()