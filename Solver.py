from z3 import *


def checkSat(s: Solver, z3_all_nodes: dict):
    if s.check() == sat:
        model = s.model()
        print(model[z3_all_nodes["1"]])
        s.add(z3_all_nodes["1"] != model[z3_all_nodes["1"]])
        print(model)
    else:
        print("No more solutions")


def applyAdmissibleFormula(s: Solver):
    pass



def simpleNodes(s: Solver, all_nodes: list(), node_defends: dict, all_nodes_z3: dict):
    for node in all_nodes:
        clause = "True"
        if node in node_defends:
            for defend in node_defends[node]:
                clause = f"And({clause}, Not(all_nodes_z3['{defend}']))"
        print(f"all_nodes_z3['{node}'] == {clause}")
        s.add(all_nodes_z3[node] == eval(clause))




def createNodes(s: Solver, all_nodes: dict):
    all_nodes_dict = dict()
    for name in all_nodes:
        all_nodes_dict[name] = Bool(f'{name}')

    # remove All-False solution
    clause = "False"
    for node in all_nodes:
        clause = f"Or({clause}, all_nodes_dict['{node}']!=False)"
    s.add(eval(clause))
    return all_nodes_dict



def solve(data: dict, all_nodes: list(), node_attacks: dict, node_defends: dict):
    s = Solver()
    all_nodes_z3 = createNodes(s, all_nodes)
    simpleNodes(s, all_nodes, node_defends, all_nodes_z3)
    checkSat(s, all_nodes_z3)





if __name__ == '__main__':
    print("Solver.py should not be executed as main. Check the Readme.md file")
