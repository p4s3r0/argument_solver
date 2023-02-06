import z3
import Debug
import Parser
from math import inf

class Solver():
    def __init__(self, parser: Parser, solution_amount: int):
        # the z3 Solver instance
        self.s = z3.Solver()
        # all solutions the solver found
        self.solution_models = list()
        # nodes in list form
        self.all_nodes = parser.all_nodes
        # nodes as dictionary, key: node , value: who attacks node
        self.node_defends = parser.node_defends
        # all nodes as z3 variables
        self.z3_all_nodes = self.createNodes()
        # amount of solutions the solver should calculate
        self.solution_amount = solution_amount



    def addRules(self, type_of_solve: str):
        '''@param type_of_solve -> stable, complete, admissible, preferred, grounded'''
        if type_of_solve == "stable":
            self.setStableExtension()
        elif type_of_solve == "complete" or type_of_solve == "grounded":
            self.setCompleteSet()
        elif type_of_solve == "admissible" or type_of_solve == "preferred":
            self.setAdmissibleSet()



    # -----------------------------------------------------------------------------
    # extracts the maximal model of the solutions
    def extractBiggestSolutions(self):
        biggest_solution = list()
        max_solution_size = 0
        for m in self.solution_models:
            curr_size = len(self.all_nodes) - len(m)
            for node in m:
                if m[node] == True:
                    curr_size += 1
            if curr_size == max_solution_size:
                biggest_solution.append(m)
            elif curr_size > max_solution_size:
                biggest_solution = [m]
                max_solution_size = curr_size
        self.solution_models = biggest_solution



    # -----------------------------------------------------------------------------
    # extracts the minimal model of the solutions
    def extractSmallestSolutions(self):
        smallest_solution = list()
        min_solution_size = inf
        for m in self.solution_models:
            curr_size = len(self.all_nodes) - len(m)
            for node in m:
                if m[node] == True:
                    curr_size += 1
            if curr_size == min_solution_size:
                smallest_solution.append(m)
            elif curr_size < min_solution_size:
                smallest_solution = [m]
                min_solution_size = curr_size
        self.solution_models = smallest_solution



    # -----------------------------------------------------------------------------
    # helper function for printSolution
    def printOneSolution(self, model: z3.Model, use_char_format: bool):
        ASCII_OFFSET = 96
        sol = list()
        for i in self.z3_all_nodes:
            if model[self.z3_all_nodes[i]] == True or model[self.z3_all_nodes[i]] == None:
                name = chr(int(i)+ASCII_OFFSET) if use_char_format else i
                sol.append(name)

        print("{", end="")
        print(*sol, sep=", ", end="}")



    # -----------------------------------------------------------------------------
    # prints the final solution with set notation
    def printSolution(self, use_char_format: bool, type_of_set: str):
        Debug.INFO("INFO", f"Solutions for {type_of_set.upper()}-set: ")
        self.printOneSolution(self.solution_models[0], use_char_format)
        for m in self.solution_models[1:]:
            print(', ', end="")
            self.printOneSolution(m, use_char_format)
        print(flush=True)
    


    # -----------------------------------------------------------------------------
    # Prints each variable of the model with = True or = False
    def printModel(self, model: z3.Model, k: int, use_char_format: bool):
        ASCII_OFFSET = 96
        Debug.INFO("SOLVER", f"solution -- [{k}] begin\n")
        for i in range(1, len(self.z3_all_nodes)+1):
            name = chr(i+ASCII_OFFSET) if use_char_format else i
            Debug.INFO("OFFSET", f"{name} = {'True' if model[self.z3_all_nodes[str(i)]] == None else model[self.z3_all_nodes[str(i)]]}")
        print()
        Debug.INFO("SOLVER", f"solution -- [{k}] end")



    # -----------------------------------------------------------------------------
    # Takes care of running the sat solver.
    def checkSat(self, use_char_format: bool):
        k = 0
        while self.s.check() == z3.sat:
            k += 1
            model = self.s.model()
            self.solution_models.append(model)
            self.negatePreviousModel(model)
            if self.solution_amount != -1 and k == self.solution_amount:
                Debug.INFO("SOLVER", f"Early stop, a total of {k} solutions were found.")
                return
        else:
            Debug.INFO("SOLVER", "No more solutions")



    # -----------------------------------------------------------------------------
    # helper function for checkSat function
    def negatePreviousModel(self, model: z3.Model):
        negate_prev_model = False
        for i in self.z3_all_nodes:
            right_side = model[self.z3_all_nodes[str(i)]]
            if model[self.z3_all_nodes[str(i)]] == None:
                right_side = True
            negate_prev_model = z3.Or(self.z3_all_nodes[str(i)] != right_side, negate_prev_model)
        self.s.add(negate_prev_model)


        
    # -----------------------------------------------------------------------------
    # Define clauses for admissible extensions
    def setAdmissibleSet(self):
        # get a: a∈A
        for a in self.all_nodes:

            # check if b exists
            if a not in self.node_defends:
                self.s.add(z3.Implies(self.z3_all_nodes[a], True))
                continue

            # (a -> ^{b:(b,a)∈R}(¬b)
            clause_left = True
            # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
            clause_right = True

            # get b: b:(b,a)∈R
            for b in self.node_defends[a]:
                clause_left = z3.And(clause_left, z3.Not(self.z3_all_nodes[str(b)]))
                
                # check if c exists
                if str(b) not in self.node_defends:
                    clause_right = z3.And(clause_right, False)
                    continue

                # get c: (c,b)∈R
                clause_right_right = False
                for c in self.node_defends[str(b)]:
                    clause_right_right = z3.Or(clause_right_right, self.z3_all_nodes[str(c)])
                    
                clause_right = z3.And(clause_right, clause_right_right)
            clause = z3.And(z3.Implies(self.z3_all_nodes[a], clause_left), z3.Implies(self.z3_all_nodes[a], clause_right))
            self.s.add(clause)



    # -----------------------------------------------------------------------------
    # Define clauses for Stable Extensions
    def setStableExtension(self):
        for a in self.all_nodes:
            clause = True
            if a not in self.node_defends:
                self.s.add(self.z3_all_nodes[str(a)] == True)
                continue
            for defend in self.node_defends[a]:
                clause = z3.And(clause, z3.Not(self.z3_all_nodes[str(defend)]))
            self.s.add(self.z3_all_nodes[a] == clause)



    # -----------------------------------------------------------------------------
    # Define clauses for Complete Extensions 
    def setCompleteSet(self):
        # get a: a∈A
        for a in self.all_nodes:

            # check if b exists
            if a not in self.node_defends:
                self.s.add(self.z3_all_nodes[a] == True)
                continue

            # (a -> ^{b:(b,a)∈R}(¬b)
            clause_left = True
            # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
            clause_right = True

            # get b: b:(b,a)∈R
            for b in self.node_defends[a]:
                clause_left = z3.And(clause_left, z3.Not(self.z3_all_nodes[str(b)]))
                
                # check if c exists
                if str(b) not in self.node_defends:
                    clause_right = z3.And(clause_right, False)
                    continue

                # get c: (c,b)∈R
                clause_right_right = False
                for c in self.node_defends[str(b)]:
                    clause_right_right = z3.Or(clause_right_right, self.z3_all_nodes[str(c)])
                    
                clause_right = z3.And(clause_right, clause_right_right)
            clause = z3.And(z3.Implies(self.z3_all_nodes[a], clause_left), self.z3_all_nodes[a] == clause_right)
            self.s.add(clause)



    # -----------------------------------------------------------------------------
    # creates the nodes as z3 variables
    def createNodes(self):
        all_nodes_dict = dict()
        for name in self.all_nodes:
            all_nodes_dict[name] = z3.Bool(f'{name}')
        return all_nodes_dict






def solve(parser: Parser, solution_amount: int, show_solution: bool, use_char_format: bool):
    Debug.DEBUG("SOLVER", f"startet calculation with {len(parser.all_nodes)} nodes and calculates {'ALL' if solution_amount == -1 else solution_amount} solutions if possible")

    solver = Solver(parser, solution_amount)
    
    # types_of_set = stable, complete, admissible, preferred, grounded
    types = [
        "admissible", #0
        "stable",     #1
        "preferred",  #2
        "complete",   #3
        "grounded"    #4
        ]
        
    type_of_set = types[0]
    solver.addRules(type_of_set)
    solver.checkSat(use_char_format)
    
    if type_of_set == "preferred": 
        solver.extractBiggestSolutions()
    elif type_of_set == "grounded":
        solver.extractSmallestSolutions()

    if show_solution: 
        for k, m in enumerate(solver.solution_models):
            solver.printModel(m, k, use_char_format)


    Debug.DEBUG("SOLVER", f"calculations done")
    solver.printSolution(use_char_format, type_of_set)
    return solver






if __name__ == '__main__':
    print("Solver.py should not be executed as main. Check the Readme.md file")
    exit()
