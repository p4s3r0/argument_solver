from z3 import *


types_of_solves = {
    "stable": False,
    "complete": True,
    "admissible": False
}


def printModel(model: Model, z3_all_nodes: dict, k: int, n: int):
    print(f"solution -- [{k}]")
    for i in range(1, n+1):
        print(f"  {i} = {model[z3_all_nodes[str(i)]]}")

# -----------------------------------------------------------------------------
def checkSat(s: Solver, z3_all_nodes: dict):
    k = 0
    while s.check() == sat:
        k += 1
        model = s.model()
        printModel(model, z3_all_nodes, k, len(z3_all_nodes))
        negate_prev_model = False
        for m in model:
            negate_prev_model = Or(z3_all_nodes[str(m)] != model[m], negate_prev_model)
        s.add(negate_prev_model)
    else:
        print("No more solutions")



# -----------------------------------------------------------------------------
def setAdmissibleSet(s: Solver):
    pass



# -----------------------------------------------------------------------------
# Define clauses for Stable Extensions
# ^{a∈A} (a <-> ^{b:(b,a)∈R}(¬b)) 
def setStableExtension(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    for node in all_nodes:
        clause = True
        if node in node_defends:
            for defend in node_defends[node]:
                clause = And(clause, Not(all_nodes_z3[str(defend)]))
        s.add(all_nodes_z3[node] == clause)




# -----------------------------------------------------------------------------
# Define clauses for Complete Extensions 
# ^{a∈A} (a -> ^{b:(b,a)∈R}(¬b) & (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R}))) 
def setCompleteSet(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    # get a: a∈A
    for a in all_nodes:

        # check if b exists
        if a not in node_defends:
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
                continue

            # get c: (c,b)∈R
            clause_right_right = False
            for c in node_defends[str(b)]:
                clause_right_right = Or(clause_right_right, all_nodes_z3[str(c)])
                
            clause_right = And(clause_right, clause_right_right)
        clause = And(Implies(all_nodes_z3[a], clause_left), Implies(all_nodes_z3[a], clause_right))
        s.add(clause)



# -----------------------------------------------------------------------------
# Second Model checking
# ^ (a -> ^( (¬b) )) , a∈A, b:(b,a)∈R 
def conflictFree(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    '''WRONG'''
    for node in all_nodes:
        clause = True
        if node in node_defends:
            for defend in node_defends[node]:
                clause = And(clause, Not(all_nodes_z3[str(defend)]))
        s.add(Implies(all_nodes_z3[node], clause))



# -----------------------------------------------------------------------------
def createNodes(s: Solver, all_nodes: dict):
    all_nodes_dict = dict()
    for name in all_nodes:
        all_nodes_dict[name] = Bool(f'{name}')

    # remove All-False solution
    clause = False
    for node in all_nodes:
        clause = Or(clause, all_nodes_dict[str(node)] != False)
    s.add(clause)
    return all_nodes_dict



def solve(data: dict, all_nodes: list(), node_attacks: dict, node_defends: dict):
    s = Solver()
    all_nodes_z3 = createNodes(s, all_nodes)
    if types_of_solves["stable"]:
        setStableExtension(s, all_nodes, node_defends, all_nodes_z3)
    elif types_of_solves["complete"]:
        setCompleteSet(s, all_nodes, node_defends, all_nodes_z3)
    elif types_of_solves["admissible"]:
        setAdmissibleSet(s, all_nodes, node_defends, all_nodes_z3)

    
    conflictFree(s, all_nodes, node_defends, all_nodes_z3)
    checkSat(s, all_nodes_z3)





if __name__ == '__main__':
    print("Solver.py should not be executed as main. Check the Readme.md file")
