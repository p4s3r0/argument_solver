import z3

s = z3.Solver()

def checkIfAdmissibleSetIsValid(S, all_nodes: dict(), node_defends: dict()):
    s.reset()
    if len(S) == 0:
        return True

    # clause left
    clause_left = True
    curr_1_and = True
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
        if a in node_defends:
            continue
        clause_right = z3.And(clause_right, z3.Not(all_nodes[str(a)]))
    
    # combined clauses
    clause = z3.And(clause_left, clause_right)
    s.add(clause)

    if s.check() == z3.sat:
        return True
    else:
        return False


def checkIfStableSetIsValid(S, all_nodes: dict(), node_defends: dict()):
    s.reset(S)
    # clause left
    clause_left = True
    

   