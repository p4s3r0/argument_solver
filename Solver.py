import z3
import Debug
import Parser



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
        '''@param type_of_solve -> stable, complete, admissible'''
        if type_of_solve == "stable":
            self.setStableExtension()
        elif type_of_solve == "complete":
            self.setCompleteSet()
        elif type_of_solve == "admissible":
            self.setAdmissibleSet()



    # -----------------------------------------------------------------------------
    # helper function for printSolution
    def printOneSolution(self, model: z3.Model, use_char_format: bool):
        ASCII_OFFSET = 96
        sol = list()
        for i in self.z3_all_nodes:
            if model[self.z3_all_nodes[i]] == True:
                name = chr(int(i)+ASCII_OFFSET) if use_char_format else i
                sol.append(name)

        print("{", end="")
        print(*sol, sep=", ", end="}")



    # -----------------------------------------------------------------------------
    # prints the final solution with set notation
    def printSolution(self, use_char_format: bool):
        Debug.INFO("INFO", "Solutions: ")
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
            Debug.INFO("OFFSET", f"{name} = {model[self.z3_all_nodes[str(i)]]}")
        print()
        Debug.INFO("SOLVER", f"solution -- [{k}] end")



    # -----------------------------------------------------------------------------
    # Takes care of running the sat solver.
    def checkSat(self, show_solution: bool, use_char_format: bool):
        # remove All-False solution
        clause = False
        for node in self.z3_all_nodes:
            clause = z3.Or(clause, node != False)
        self.s.add(clause)

        k = 0
        while self.s.check() == z3.sat:
            k += 1
            model = self.s.model()
            self.solution_models.append(model)
            if show_solution: self.printModel(model, k, use_char_format)
            self.negatePreviousModel(model)
            if self.solution_amount != -1 and k == self.solution_amount:
                Debug.INFO("SOLVER", f"Early stop, a total of {k} solutions were found.")
                return
        else:
            if show_solution: Debug.INFO("SOLVER", "No more solutions")


    # -----------------------------------------------------------------------------
    # helper function for checkSat functino
    def negatePreviousModel(self, model: z3.Model):
        negate_prev_model = False
        for m in model:
            negate_prev_model = z3.Or(self.z3_all_nodes[str(m)] != model[m], negate_prev_model)
        self.s.add(negate_prev_model)


        
    # -----------------------------------------------------------------------------
    # Define clauses for admissible extensions
    def setAdmissibleSet(self):
        pass



    # -----------------------------------------------------------------------------
    # Define clauses for Stable Extensions
    def setStableExtension(self):
        for a in self.all_nodes:
            clause = True
            if a not in self.node_defends:
                self.s.add(self.z3_all_nodes[str(a)] == True)
                continue
            for defend in self.node_defends[a]:
                clause = And(clause, Not(self.z3_all_nodes[str(defend)]))
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
                    self.s.add(self.z3_all_nodes[str(b)] == True)
                    continue

                # get c: (c,b)∈R
                clause_right_right = False
                for c in self.node_defends[str(b)]:
                    clause_right_right = z3.Or(clause_right_right, self.z3_all_nodes[str(c)])
                    
                clause_right = z3.And(clause_right, clause_right_right)
            clause = z3.And(z3.Implies(self.z3_all_nodes[a], clause_left), z3.Implies(self.z3_all_nodes[a], clause_right))
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
    # types_of_solves = stable, complete, admissible
    solver.addRules("complete")
    solver.checkSat(show_solution, use_char_format)

    Debug.DEBUG("SOLVER", f"calculations done")
    solver.printSolution(use_char_format)
    return solver






if __name__ == '__main__':
    print("Solver.py should not be executed as main. Check the Readme.md file")
    exit()
