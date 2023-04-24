# This file is part of IPAFAIR, an incremental API for AF solvers.
# See LICENSE.md for rights to use this software.
import ipafair
from typing import List

import z3
import Parser
import KSolver
import Exceptions as Exception


# k iterations
k = 3

class AFSolver(ipafair.AFSolver):
    # Initializes an AFSolver instance using the initial AF provided in af_file
    # and the semantics sigma ("CO", "PR", or "ST").
    # If af_file is None, the initial AF is assumed to be empty.
    # If af_file is not a valid file, changes the state of AFSolver to ERROR.
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

        # check for argumentation set
        if sigma == "PR":
            raise NotImplementedError
        if sigma not in ["CO", "ST"]:
            raise Exception.WrongArgumentationSet

        # type of set
        self.set_type = sigma
        # solutions pool
        self.solutions = list()

        # temporary variable for current result
        self.curr_solution = False



    # Deletes an AFSolver instance.
    def __del__(self):
        del self.s
        del self.parser
        del self.all_nodes
        del self.node_defends
        del self.z3_all_nodes
        del self.solution_amount
        del self.set_type
        del self.solutions
        del self.curr_solution
        


    # Adds the argument arg to the current AF instance.
    def add_argument(self, arg: int):
        if str(arg) in self.all_nodes:
            raise Exception.ArgumentWasAddedBefore

        self.all_nodes.append(str(arg))
        self.z3_all_nodes[str(arg)] = z3.Bool(f'{arg}')
        


    # Deletes the argument arg from the current AF instance.
    def del_argument(self, arg: int):
        if str(arg) not in self.all_nodes:
            raise Exception.ArgumentWasNotAddedBefore

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
    def add_attack(self, source: int, target: int):
        if str(source) not in self.all_nodes or str(target) not in self.all_nodes:
            raise Exception.AttackWithNotRegisteredArguments

        if str(target) in self.node_defends:
            # avoid adding same attack again
            if str(source) not in self.node_defends[str(target)]:
                self.node_defends[str(target)].append(source)
        else:
            self.node_defends[str(target)] = [source]



    # Deletes the attack (source,target) from the current AF instance.
    def del_attack(self, source: int, target: int):
        if str(source) not in self.all_nodes or str(target) not in self.all_nodes:
            raise Exception.AttackWithNotRegisteredArguments
        
        if source in self.node_defends[str(target)]:
            self.node_defends[str(target)].remove(source)
        else: 
            raise Exception.AttackWasNotRegistered

        if len(self.node_defends[str(target)]) == 0:
            del self.node_defends[str(target)]
        


    # Solves the current AF instance under the specified semantics in the
    # credulous reasoning mode under assumptions that all arguments in assumps
    # are contained in an extension.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    def solve_cred(self, assumps: List[int]) -> bool:
        for curr_assump in assumps:
            if str(curr_assump) not in self.all_nodes:
                raise Exception.AttackWithNotRegisteredArguments
        
        # check previous solutions if they fit the assumptions and if they are still valid
        solution = self.checkPreviousSolutionsForCredulous(assumps)
        if solution != False:
            self.curr_solution = solution
            return True
        
        # calculate new solutions with assumptions = True
        previous_solution_amount = len(self.solutions)
        self.addRules()
        for assumption in assumps:
            self.s.add(self.z3_all_nodes[str(assumption)] == True)

        self.checkSat()

        if len(self.solutions) > previous_solution_amount:
            self.curr_solution = self.solutions[previous_solution_amount]
            return True
        else:
            return False
        


    # Solves the current AF instance under the specified semantics in the
    # skeptical reasoning mode under assumptions that all arguments in assumps
    # are contained in all extensions.
    # Returns True if the answer is "yes" and False if the answer is "no".
    # Other return codes indicate that the solver is in state ERROR.
    def solve_skept(self, assumps: List[int]) -> bool:
        for curr_assump in assumps:
            if str(curr_assump) not in self.all_nodes:
                raise Exception.AttackWithNotRegisteredArguments
            
        solution = self.checkPreviousSolutionsForSkeptical(assumps)
        if solution != True: 
            self.curr_solution = solution
            return False
        
        previous_solution_amount = len(self.solutions)
        self.addRules()
        assumption_negation = False
        for assumption in assumps:
            assumption_negation = z3.Or(z3.Not(self.z3_all_nodes[str(assumption)]), assumption_negation)
        
        self.s.add(assumption_negation)
        self.checkSat()

        if len(self.solutions) > previous_solution_amount:
            self.curr_solution = self.solutions[previous_solution_amount]
            return False
        else:
            return True



    # If the previous call of solve_cred returned True, or the previous call to
    # solve_skept returned False, returns the witnessing extension.
    def extract_witness(self) -> List[int]:
        if self.curr_solution == False: 
            raise Exception.WitnessCallBeforeCredSkeptCall
        return [int(node) for node in self.curr_solution]



# --------------------------------------- BACKEND -------------------------------------------------



    # -----------------------------------------------------------------------------
    # CREDULOUS
    # Checks if we have a valid precomputed solution. If we dont find a solution 
    # along the precomputed solutions which corresponds to the assumptions, 
    # we compute another k solutions. If we found a solution, we recheck if the 
    # solution is still valid with the current model. If yes, select solution, if not
    # delete solution of the pool and keep searching.
    def checkPreviousSolutionsForCredulous(self, assumptions):
        remove_solutions = list()
        for solution in self.solutions:
            if all(str(assumption) in solution for assumption in assumptions):
                if self.checkIfSolutionIsValid(solution):
                    return solution
                else: 
                    remove_solutions.append(solution)

        # remove invalid solutions from valid solutions pool
        for remove_sol in remove_solutions:
            self.solutions.remove(remove_sol)

        return False



    # -----------------------------------------------------------------------------
    # SKEPTICAL
    # Checks if we have a valid precomputed solution. If we dont find a solution 
    # along the precomputed solutions which corresponds to the assumptions, 
    # we compute another k solutions. If we found a solution, we recheck if the 
    # solution is still valid with the current model. If yes, select solution, if not
    # delete solution of the pool and keep searching.
    def checkPreviousSolutionsForSkeptical(self, assumptions):
        remove_solutions = list()

        for solution in self.solutions:
            for element in assumptions:
                if str(element) not in solution:
                    if self.checkIfSolutionIsValid(solution):
                        return solution
                    else:
                        remove_solutions.append(solution)
                        break

        # remove invalid solutions from valid solutions
        for remove_sol in remove_solutions:
            self.solutions.remove(remove_sol)

        return True



    # -----------------------------------------------------------------------------
    # Runs another SAT-Solver to check, if the precomputed solution is still valid
    # in the current model. The other SAT-Solver is defined in KSolver.py
    def checkIfSolutionIsValid(self, solution):
        checkFunction = None
        if self.set_type == "CO":
            checkFunction = KSolver.checkIfCompleteSetIsValid
        elif self.set_type == "ST":
            checkFunction = KSolver.checkIfStableSetIsValid

        return checkFunction(solution, self.z3_all_nodes, self.node_defends)
            
     

    # -----------------------------------------------------------------------------
    # Initializes the SAT-Solver with the specified Set.
    def addRules(self):
        self.s.reset()
        if self.set_type == "CO":
            self.setCompleteSet()
        elif self.set_type == "ST":
            self.setStableExtension()



    # -----------------------------------------------------------------------------
    # Runs the SAT-Solver and produces k-solutions
    def checkSat(self):
        k = 0
        while self.s.check() == z3.sat:
            k += 1
            model = self.s.model()
            self.solutions.append(self.extractSolution(model))
            self.negatePreviousModel(model)
            if self.solution_amount != -1 and k == self.solution_amount:
                return



    # -----------------------------------------------------------------------------
    # Extracts the Solution of the SAT-Solver and saves it into a Boolean format.
    # Z3 only specifies Boolean Variables, which have a clear True/False specification.
    # So if a variable can be both (True/False), it sets the vairable to None, which
    # would break our interface.
    def extractSolution(self, model):
        curr_sol = list()
        for i in self.z3_all_nodes:
            curr_bool = model[self.z3_all_nodes[str(i)]]
            if  curr_bool == None or curr_bool== True:
                curr_sol.append(i)
        return curr_sol



    # -----------------------------------------------------------------------------
    # Helper function for checkSat method. This function negates the found model,
    # such that the SAT-Solver finds other models. 
    def negatePreviousModel(self, model: z3.Model):
        negate_prev_model = False
        for i in self.z3_all_nodes:
            right_side = model[self.z3_all_nodes[str(i)]]
            if model[self.z3_all_nodes[str(i)]] == None:
                right_side = True
            negate_prev_model = z3.Or(self.z3_all_nodes[str(i)] != right_side, negate_prev_model)
        self.s.add(negate_prev_model)



    # -----------------------------------------------------------------------------
    # Defines the Stable Rules for the solver.
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
    # Defines the Complete Rules for the solver. 
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
    # Creates the nodes as z3 variables
    def createNodes(self):
        all_nodes_dict = dict()
        for name in self.all_nodes:
            all_nodes_dict[name] = z3.Bool(f'{name}')
        return all_nodes_dict



# -----------------------------------------------------------------------------
# Main Guard
if __name__ == '__main__':
    raise Exception.LibraryWasRunAsMain