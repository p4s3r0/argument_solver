# -----------------------------------------------------------------------------
# KSOLVER.PY
# This is a second SAT-Solver which checks if a solution is still valid with
# the current model.
# -----------------------------------------------------------------------------
import z3
from . import Exceptions as Exception

s = z3.Solver()
# -----------------------------------------------------------------------------
# Checks if the solution is still in admissible Set
def checkIfAdmissibleSetIsValid(S, all_nodes: dict(), node_defends: dict()):
    s.reset()
    if len(S) == 0:
        return True

    # clause left
    clause_left = True
    for a in S:
        curr_2_and = True
        # get b
        if str(a) in node_defends:
            for b in node_defends[str(a)]:
                # get c
                curr_3_or = False
                if str(b) in node_defends:
                    for c in node_defends[str(b)]:
                        curr_3_or = z3.Or(curr_3_or, all_nodes[str(c)])

                curr_inner_par = z3.And(z3.Not(all_nodes[str(b)]), curr_3_or)
                curr_2_and = z3.And(curr_2_and, curr_inner_par)
        curr_outer_part = z3.And(all_nodes[str(a)], curr_2_and)
        clause_left = z3.And(clause_left, curr_outer_part)

    # clause right ^{a not in S} ¬a
    clause_right = True
    for a in all_nodes:
        if a in S:
            continue
        clause_right = z3.And(clause_right, z3.Not(all_nodes[str(a)]))
    
    # combined clauses
    clause = z3.And(clause_left, clause_right)
    s.add(clause)

    if s.check() == z3.sat:
        return True
    else:
        return False



# -----------------------------------------------------------------------------
# Checks if the solution is still in stable Set
def checkIfStableSetIsValid(S, all_nodes: dict(), node_defends: dict()):
    s.reset()
    # clause left
    clause_left = True
    for a in S:
        if str(a) not in all_nodes:
            continue
        clause_left_outter_and = True
        clause_left_inner_and = True
        if str(a) in node_defends:
            for b in node_defends[str(a)]:
                clause_left_inner_and = z3.And(clause_left_inner_and, z3.Not(all_nodes[str(b)]))
        
        clause_left_outter_and = z3.And(all_nodes[str(a)], clause_left_inner_and)
        clause_left = z3.And(clause_left_outter_and, clause_left)

    clause_right = True
    for a in all_nodes:
        if a in S:
            continue

        clause_right_inner_and = False
        clause_right_or = False
        if str(a) in node_defends:
            for b in node_defends[str(a)]:
                clause_right_or = z3.Or(all_nodes[str(b)], clause_right_or)   
            clause_right_inner_and = z3.And(z3.Not(all_nodes[str(a)]), clause_right_or)
        clause_right = z3.And(clause_right_inner_and, clause_right)

    clause = z3.And(clause_left, clause_right)
    s.add(clause)

    if s.check() == z3.sat:
        return True
    else:
        return False

    


# -----------------------------------------------------------------------------
# Checks if the solution is still in complete Set
def checkIfCompleteSetIsValid(S, all_nodes: dict(), node_defends: dict()):
    s.reset()

    left_clause = True
    for a in S:
        if str(a) not in all_nodes:
            continue
        inner_2_and = True
        if str(a) in node_defends:
            for b in node_defends[str(a)]:
                inner_2_and = z3.And(z3.Not(all_nodes[str(b)]), inner_2_and)

        left_second_part = True
        if str(a) in node_defends:
            for b in node_defends[str(a)]:
                inner_3_and = True
                inner_4_or = False
                if str(b) in node_defends:
                    for c in node_defends[str(b)]:
                        inner_4_or = z3.Or(all_nodes[str(c)], inner_4_or)
                inner_3_and = z3.And(inner_4_or, inner_3_and)
                left_second_part = z3.And(inner_3_and, left_second_part)

        left_clause = z3.And(left_clause, z3.And(z3.And(all_nodes[str(a)], inner_2_and), left_second_part))
    
    right_clause = True
    for a in all_nodes:
        if a in S:
            continue
        right_clause_inner = True
        inner_6_and = True
        if str(a) in node_defends:
            for b in node_defends[(str(a))]:
                inner_7_or = False
                if str(b) in node_defends:
                    for c in node_defends[str(b)]:
                        inner_7_or = z3.Or(all_nodes[str(c)] , inner_7_or)
                inner_6_and = z3.And(inner_6_and, inner_7_or)
        
        right_clause_inner = z3.And(z3.Not(all_nodes[str(a)]), z3.Not(inner_6_and))
        right_clause = z3.And(right_clause, right_clause_inner)

    clause = z3.And(left_clause, right_clause)
    s.add(clause)

    if s.check() == z3.sat:
        return True
    else:
        return False



# -----------------------------------------------------------------------------
# Main Guard
if __name__ == "__main__":
    raise Exception.LibraryWasRunAsMain