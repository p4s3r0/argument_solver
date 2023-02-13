# This file is part of IPAFAIR, an incremental API for AF solvers.
# See LICENSE.md for rights to use this software.
from abc import ABC, abstractmethod
from typing import Tuple, List

import z3
import Debug
import Parser
import KSolver
from math import inf

# k iterations
k = 100

class AFSolver():

    # Initializes an AFSolver instance using the initial AF provided in af_file
    # and the semantics sigma ("CO", "PR", or "ST").
    # If af_file is None, the initial AF is assumed to be empty.
    # If af_file is not a valid file, changes the state of AFSolver to ERROR.
    @abstractmethod
    def __init__(self, sigma: str, af_file: str = None):
        # the z3 Solver instance
        self.s = z3.Solver()

        # parse the input
        self.parser = Parser.parse(af_file)
        # nodes in list form
        self.all_nodes = self.parser.all_nodes
        # nodes as dictionary, key: node , value: who attacks node
        self.node_defends = self.parser.node_defends
        # all nodes as z3 variables
        self.z3_all_nodes = self.createNodes()

        # amount of solutions the solver should calculate
        self.solution_amount = k
        # type of set
        self.set_type = sigma
        #solutions
        self.solutions = list()


    # Deletes an AFSolver instance.
    @abstractmethod
    def __del__(self):
        print("TODO delete solver")

    # Adds the argument arg to the current AF instance.
    @abstractmethod
    def add_argument(self, arg: int):
        self.all_nodes.append(str(arg))
        self.z3_all_nodes[str(arg)] = z3.Bool(f'{arg}')
        

    # Deletes the argument arg from the current AF instance.
    @abstractmethod
    def del_argument(self, arg: int):
        self.all_nodes.remove(str(arg))
        del self.z3_all_nodes[str(arg)]

    # Adds the attack (source,target) to the current AF instance.
    @abstractmethod
    def add_attack(self, source: int, target: int):
        if str(target) in self.node_defends:
            self.node_defends[str(target)].append(source)
        else:
            self.node_defends[str(target)] = [source]

    # Deletes the attack (source,target) from the current AF instance.
    @abstractmethod
    def del_attack(self, source: int, target: int):
        del self.node_defends[str(target)]

    # Solves the current AF instance under the specified semantics in the
    # credulous reasoning mode under assumptions that all arguments in assumps
    # are contained in an extension.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    @abstractmethod
    def solve_cred(self, assumps: List[int]) -> bool:
        if len(self.solutions) > 0:
            self.checkIfSolutionsAreValid()
        
        self.addRules()
        self.checkSat()
        


    # Solves the current AF instance under the specified semantics in the
    # skeptical reasoning mode under assumptions that all arguments in assumps
    # are contained in all extensions.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    @abstractmethod
    def solve_skept(self, assumps: List[int]) -> bool:
        raise NotImplementedError

    # If the previous call of solve_cred returned True, or the previous call to
    # solve_skept returned False, returns the witnessing extension.
    @abstractmethod
    def extract_witness(self) -> List[int]:
        raise NotImplementedError







    # MY IMPLEMENTION
    def checkIfSolutionsAreValid(self):
        checkFunction = None
        if self.set_type == "ST":
            checkFunction = KSolver.checkIfStableSetIsValid
        elif self.set_type == "PR":
            checkFunction = KSolver.checkIfPreferredSetIsValid
        elif self.set_type == "CO":
            checkFunction = KSolver.checkIfCompleteSetIsValid

        delete_solutions = list()
        for solution in self.solutions:
            if not checkFunction(solution, self.z3_all_nodes, self.node_defends): print("removed solution", solution);delete_solutions.append(solution)
            
        for remove_solution in delete_solutions:
            self.solutions.remove(remove_solution)

            


    def addRules(self):
        '''@param type_of_solve -> stable, complete, admissible, preferred, grounded'''
        if self.set_type == "ST":
            self.setStableExtension()
        elif self.set_type == "CO":
            self.setCompleteSet()
        elif self.set_type ==  "PR":
            self.setAdmissibleSet(self.all_nodes)







    # -----------------------------------------------------------------------------
    # prints the final solution with set notation
    def printSolution(self):
        Debug.INFO("INFO", f"Solutions for {self.set_type.upper()}-set: ")
        for j, curr_sol in enumerate(self.solutions):
            print("{", end="")
            for i, curr_bool in enumerate(curr_sol):
                print(curr_bool, end = ', ' if i != len(curr_sol) - 1 else '')
            print("}", end = ', ' if j != len(self.solutions) - 1 else '')
        print(flush=True)



    # -----------------------------------------------------------------------------
    # Takes care of running the sat solver.
    def checkSat(self):
        k = 0
        while self.s.check() == z3.sat:
            k += 1
            model = self.s.model()
            self.solutions.append(self.extractSolution(model))
            self.negatePreviousModel(model)
            if self.solution_amount != -1 and k == self.solution_amount:
                Debug.INFO("SOLVER", f"Early stop, a total of {k} solutions were found.")
                return
        else:
            Debug.INFO("SOLVER", "No more solutions")



    def extractSolution(self, model):
        curr_sol = list()
        for i in self.z3_all_nodes:
            curr_bool = model[self.z3_all_nodes[str(i)]]
            if  curr_bool == None or curr_bool== True:
                curr_sol.append(i)
        return curr_sol

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
    def setAdmissibleSet(self, nodes: List):
        # get a: a∈A
        for a in nodes:

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


