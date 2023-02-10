from Solver import AFSolver
import os

path = os.path.dirname(os.path.abspath("/Users/p4s3r0/Desktop/argument_solver/inputs/pims.af"))
s = AFSolver("CO", os.path.join(path, "pims.af"))
s.solve_cred([0])
s.printSolution()

print("end of program")
'''
assert(s.solve_cred([1]))
assert(not s.solve_cred([2]))

s.del_attack(1,2)
assert(s.solve_cred([1]))
assert(s.solve_cred([2]))

s.add_argument(3)
s.add_attack(3, 2)
s.add_attack(2, 1)
assert(s.solve_cred([1]))
assert(not s.solve_cred([2]))
assert(s.solve_cred([3]))

s.del_argument(1)
s.add_argument(4)
s.add_attack(4, 3)
s.add_attack(3, 4)
assert(s.solve_cred([2]))
assert(s.solve_cred([3]))
assert(not s.solve_skept([4]))
'''