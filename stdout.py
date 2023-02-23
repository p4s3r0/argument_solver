# -----------------------------------------------------------------------------
# STDOUT.PY
# Used for correct competition output.
# -----------------------------------------------------------------------------
import Debug

# -----------------------------------------------------------------------------
# prints YES and the solution in set format
def YES_WITH_SOLUTION(solution: list()):
    print("YES {", end="")
    for i, curr_sol in enumerate(solution):
                print(curr_sol, end = ', ' if i != len(solution) - 1 else '')
    print("}")
    print(flush=True, end="")



# -----------------------------------------------------------------------------
# prints NO and the solution in set format
def NO_WITH_SOLUTION(solution: list()):
    print("NO {", end="")
    for i, curr_sol in enumerate(solution):
                print(curr_sol, end = ', ' if i != len(solution) - 1 else '')
    print("}")
    print(flush=True, end="")



# -----------------------------------------------------------------------------
# prints NO
def NO():
    print("NO")
    print(flush=True, end="")



# -----------------------------------------------------------------------------
# prints YES
def YES():
    print("YES")
    print(flush=True, end="")


# -----------------------------------------------------------------------------
# Main Guard
if __name__ == '__main__':
    Debug.ERROR("Parser.py should not be executed as main. Check the Readme.md")