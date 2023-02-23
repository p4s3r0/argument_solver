# This file is part of IPAFAIR, an incremental API for AF solvers.
# See LICENSE.md for rights to use this software.
from abc import ABC, abstractmethod
from typing import Tuple, List

import z3
import Debug
import Parser
import KSolver
import stdout
from math import inf

# k iterations
k = 10

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
        pass
    # Adds the argument arg to the current AF instance.
    @abstractmethod
    def add_argument(self, arg: int):
        if str(arg) in self.all_nodes:
            return
        self.all_nodes.append(str(arg))
        self.z3_all_nodes[str(arg)] = z3.Bool(f'{arg}')
        


    # Deletes the argument arg from the current AF instance.
    @abstractmethod
    def del_argument(self, arg: int):
        if str(arg) not in self.all_nodes:
            print("argument is not found.")
            return

        self.all_nodes.remove(str(arg))
        del self.z3_all_nodes[str(arg)]
        if str(arg) in self.node_defends:
            del self.node_defends[str(arg)]

        for defender in self.node_defends:
            curr_key_del = list()
            for attacker in self.node_defends[str(defender)]:
                if attacker == arg:
                    curr_key_del.append(attacker)
            for delete_ele in curr_key_del:
                self.node_defends[str(defender)].remove(delete_ele)



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
        if source in self.node_defends[str(target)]:
            self.node_defends[str(target)].remove(source)
        else: 
            Debug.ERROR("del_attack attack was not registered")

        if len(self.node_defends[str(target)]) == 0:
            del self.node_defends[str(target)]
        


    # Solves the current AF instance under the specified semantics in the
    # credulous reasoning mode under assumptions that all arguments in assumps
    # are contained in an extension.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    @abstractmethod
    def solve_cred(self, assumps: List[int]) -> bool:
        # check previous solutions if they fit the assumptions and if they are still valid
        solution = self.checkPreviousSolutionsForCredulous(assumps)
        if solution != False:
            stdout.BROADCAST(f"YES {solution}")
        
        previous_solution_amount = len(self.solutions)
        self.addRules()
        for assumption in assumps:
            self.s.add(self.z3_all_nodes[str(assumption)] == True)

        self.checkSat()

        if len(self.solutions) > previous_solution_amount:
            stdout.YES_WITH_SOLUTION(self.solutions[previous_solution_amount])
        else:
            stdout.NO()
        


    # Solves the current AF instance under the specified semantics in the
    # skeptical reasoning mode under assumptions that all arguments in assumps
    # are contained in all extensions.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    @abstractmethod
    def solve_skept(self, assumps: List[int]) -> bool:
        solution = self.checkPreviousSolutionsForSkeptical(assumps)
        if solution != True: 
            stdout.NO_WITH_SOLUTION(solution)
            return
        
        previous_solution_amount = len(self.solutions)
        self.addRules()
        assumption_negation = False
        for assumption in assumps:
            assumption_negation = z3.Or(z3.Not(self.z3_all_nodes[str(assumption)]), assumption_negation)
        
        self.s.add(assumption_negation)
        self.checkSat()

        if len(self.solutions) > previous_solution_amount:
            stdout.NO_WITH_SOLUTION(self.solutions[previous_solution_amount])
        else:
            stdout.YES()

    # If the previous call of solve_cred returned True, or the previous call to
    # solve_skept returned False, returns the witnessing extension.
    @abstractmethod
    def extract_witness(self) -> List[int]:
        raise NotImplementedError







    # MY IMPLEMENTION
    def checkPreviousSolutionsForCredulous(self, assumptions):
        remove_solutions = list()
        for solution in self.solutions:
            if all(str(assumption) in solution for assumption in assumptions):
                if self.checkIfSolutionIsValid(solution):
                    return solution
                else: 
                    remove_solutions.append(solution)

        # remove invalid solutions from valid solutions
        for remove_sol in remove_solutions:
            self.solutions.remove(remove_sol)

        return False



    def checkPreviousSolutionsForSkeptical(self, assumptions):
        remove_solutions = list()

        for solution in self.solutions:
            for element in assumptions:
                if element not in solution:
                    if self.checkIfSolutionIsValid(solution):
                        return solution
                    else:
                        remove_solutions.append(solution)
                        break

        # remove invalid solutions from valid solutions
        for remove_sol in remove_solutions:
            self.solutions.remove(remove_sol)

        return True



    def checkIfSolutionIsValid(self, solution):
        checkFunction = None
        if self.set_type == "CO":
            checkFunction = KSolver.checkIfCompleteSetIsValid
        elif self.set_type == "ST":
            checkFunction = KSolver.checkIfStableSetIsValid
        elif self.set_type == "PR":
            checkFunction = KSolver.checkIfPreferredSetIsValid
        
        else:
            print("WRONG SET")
            exit()

        if not checkFunction(solution, self.z3_all_nodes, self.node_defends): 
            Debug.INFO("SOLVER", f"removed solution {solution}")
            
     

    def addRules(self):
        '''@param type_of_solve -> stable, complete, admissible, preferred, grounded'''
        self.s.reset()
        if self.set_type == "CO":
            self.setCompleteSet()
        elif self.set_type == "ST":
            self.setStableExtension()
        elif self.set_type ==  "PR":
            self.setAdmissibleSet(self.all_nodes)
        else:
            print("WRONG SET")
            exit()



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
        for a in self.all_nodes:
            left_2_and_clause = True
            if str(a) in self.node_defends:
                for b in self.node_defends[str(a)]:
                    left_2_and_clause = z3.And(left_2_and_clause, z3.Not(self.z3_all_nodes[str(b)]))
            left_clause = z3.Implies(self.z3_all_nodes[str(a)], left_2_and_clause)

            right_3_and_clause = True
            if str(a) in self.node_defends:
                for b in self.node_defends[str(a)]:
                    right_4_or_clause = False
                    if str(b) in self.node_defends:
                        for c in self.node_defends[str(b)]:
                            right_4_or_clause = z3.Or(right_4_or_clause, self.z3_all_nodes[str(c)])
                    right_3_and_clause = z3.And(right_3_and_clause, right_4_or_clause)
            
            
            right_clause = (self.z3_all_nodes[str(a)] == right_3_and_clause)
            clause = z3.And(left_clause, right_clause)
            self.s.add(clause)

        

    # -----------------------------------------------------------------------------
    # creates the nodes as z3 variables
    def createNodes(self):
        all_nodes_dict = dict()
        for name in self.all_nodes:
            all_nodes_dict[name] = z3.Bool(f'{name}')
        return all_nodes_dict


