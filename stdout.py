def YES_WITH_SOLUTION(solution: list()):
    print("YES {", end="")
    for i, curr_sol in enumerate(solution):
                print(curr_sol, end = ', ' if i != len(solution) - 1 else '')
    print("}")
    print(flush=True, end="")

def NO_WITH_SOLUTION(solution: list()):
    print("NO {", end="")
    for i, curr_sol in enumerate(solution):
                print(curr_sol, end = ', ' if i != len(solution) - 1 else '')
    print("}")
    print(flush=True, end="")

def NO():
    print("NO")
    print(flush=True, end="")


def YES():
    print("YES")
    print(flush=True, end="")



    

def BROADCAST(text: str):
    print(text)