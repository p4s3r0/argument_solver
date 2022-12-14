from z3 import *
import Debug

# Which set should be computed
types_of_solves = {
    "stable": False,
    "complete": True,
    "admissible": False
}


# all found models 
solution_models = list()



# -----------------------------------------------------------------------------
# helper function for printSolution
def printOneSolution(model: Model, z3_all_nodes: dict, n: int, char_format: bool):
    ASCII_OFFSET = 96
    sol = list()
    for i in z3_all_nodes:
        if model[z3_all_nodes[i]] == True:
            name = chr(int(i)+ASCII_OFFSET) if char_format else i
            sol.append(name)

    print("{", end="")
    print(*sol, sep=", ", end="}")



# -----------------------------------------------------------------------------
# prints the final solution with set notation
def printSolution(z3_all_nodes: dict, char_format: bool):
    Debug.INFO("INFO", "Solutions: ")
    printOneSolution(solution_models[0], z3_all_nodes, len(z3_all_nodes), char_format)
    for m in solution_models[1:]:
        print(', ', end="")
        printOneSolution(m, z3_all_nodes, len(z3_all_nodes), char_format)
    print(flush=True)
    


# -----------------------------------------------------------------------------
# Prints each variable of the model with = True or = False
def printModel(model: Model, z3_all_nodes: dict, k: int, n: int, char_format: bool):
    ASCII_OFFSET = 96
    Debug.INFO("SOLVER", f"solution -- [{k}] begin\n")
    for i in range(1, n+1):
        name = chr(i+ASCII_OFFSET) if char_format else i
        Debug.INFO("OFFSET", f"{name} = {model[z3_all_nodes[str(i)]]}")
    print()
    Debug.INFO("SOLVER", f"solution -- [{k}] end")




# -----------------------------------------------------------------------------
# Takes care of running the sat solver.
def checkSat(s: Solver, solution_amount: int, z3_all_nodes: dict, show_solution: bool, char_format: bool):
    # remove All-False solution
    clause = False
    for node in z3_all_nodes:
        clause = Or(clause, node != False)
    s.add(clause)

    k = 0
    while s.check() == sat:
        k += 1
        model = s.model()
        solution_models.append(model)
        if show_solution: printModel(model, z3_all_nodes, k, len(z3_all_nodes), char_format)
        negate_prev_model = False
        for m in model:
            negate_prev_model = Or(z3_all_nodes[str(m)] != model[m], negate_prev_model)
        s.add(negate_prev_model)
        if solution_amount != -1 and k == solution_amount:
            Debug.INFO("SOLVER", f"Early stop, a total of {k} solutions were found.")
            return
    else:
        if show_solution: Debug.INFO("SOLVER", "No more solutions")



# -----------------------------------------------------------------------------
def setAdmissibleSet(s: Solver):
    pass



# -----------------------------------------------------------------------------
# Define clauses for Stable Extensions
# @s            -> The z3 solver
# @all_nodes    -> a list with all nodes names as integer
# @node_defends -> a dictionary with key the node and value a list of all nodes who attack the key
# @all_nodes_z3 -> all z3 variable nodes in dictionary format 
def setStableExtension(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    for a in all_nodes:
        clause = True
        if a not in node_defends:
            s.add(all_nodes_z3[str(a)] == True)
            continue
        for defend in node_defends[a]:
            clause = And(clause, Not(all_nodes_z3[str(defend)]))
        s.add(all_nodes_z3[a] == clause)




# -----------------------------------------------------------------------------
# Define clauses for Complete Extensions 
# @s            -> The z3 solver
# @all_nodes    -> a list with all nodes names as integer
# @node_defends -> a dictionary with key the node and value a list of all nodes who attack the key
# @all_nodes_z3 -> all z3 variable nodes in dictionary format 
def setCompleteSet(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    # get a: a∈A
    for a in all_nodes:

        # check if b exists
        if a not in node_defends:
            s.add(all_nodes_z3[a] == True)
            continue

        # (a -> ^{b:(b,a)∈R}(¬b)
        clause_left = True
        # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
        clause_right = True

        # get b: b:(b,a)∈R
        for b in node_defends[a]:
            clause_left = And(clause_left, Not(all_nodes_z3[str(b)]))
            # check if c exists
            if str(b) not in node_defends:
                s.add(all_nodes_z3[str(b)] == True)
                continue

            # get c: (c,b)∈R
            clause_right_right = False
            for c in node_defends[str(b)]:
                clause_right_right = Or(clause_right_right, all_nodes_z3[str(c)])
                
            clause_right = And(clause_right, clause_right_right)
        clause = And(Implies(all_nodes_z3[a], clause_left), Implies(all_nodes_z3[a], clause_right))
        s.add(clause)



# -----------------------------------------------------------------------------
# creates the nodes as z3 variables and returns them
# @s         -> the z3 solver
# @all_nodes -> a dictionary with all defined nodes
def createNodes(s: Solver, all_nodes: dict):
    all_nodes_dict = dict()
    for name in all_nodes:
        all_nodes_dict[name] = Bool(f'{name}')
    return all_nodes_dict



def solve(data: dict, all_nodes: list(), node_attacks: dict, node_defends: dict, solution_amount: int, show_solution: bool, char_format: bool):
    Debug.DEBUG("SOLVER", f"startet calculation with {len(all_nodes)} nodes and calculates {'ALL' if solution_amount == -1 else solution_amount} solutions if possible")
    s = Solver()
    z3_all_nodes = createNodes(s, all_nodes)
    if types_of_solves["stable"]:
        setStableExtension(s, all_nodes, node_defends, z3_all_nodes)
    elif types_of_solves["complete"]:
        setCompleteSet(s, all_nodes, node_defends, z3_all_nodes)
    elif types_of_solves["admissible"]:
        setAdmissibleSet(s, all_nodes, node_defends, z3_all_nodes)

    checkSat(s, solution_amount, z3_all_nodes, show_solution, char_format)
    Debug.DEBUG("SOLVER", f"calculations done")
    printSolution(z3_all_nodes, char_format)






if __name__ == '__main__':
    print("Solver.py should not be executed as main. Check the Readme.md file")
    exit()
