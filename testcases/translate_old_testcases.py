# -----------------------------------------------------------------------------
# TRANSLATE_OLD_TESTCASES.PY
# This script translates the old testcases from 2019 into the new format.
# USAGE: Just place the files of the same test (.apx, .apx.arg, .apxm, .tgf)
#        from [http://argumentationcompetition.org/2019/files.html] -> iccma-instances.tar.gz
#        and the results ({name}.apx-DC-CO-D.out, {name}.apx-DC-ST-D.out,
#                         {name}.apx-DS-CO-D.out, {name}.apx-DS-ST-D.out)
#        from [http://argumentationcompetition.org/2019/files.html] -> reference-results.tar.gz
#        into the testcases/ folder and then run the script after setting the 
#        raw_test_name and test_num variable. The testcases are then moved
#        accordingly to the correct folders.
# -----------------------------------------------------------------------------
import shutil
import os

# -----------------------------------------------------------------------------
raw_test_name = "A-1-admbuster_4000"
test_num = "6"
# -----------------------------------------------------------------------------



# -----------------------------------------------------------------------------
# files for input / output
inp_file = f"{raw_test_name}.tgf"
out_file = f"{test_num}_{raw_test_name}.af"
dic_file = f"{raw_test_name}.dic"
mod_inp_file = f"{raw_test_name}.apxm"
# -----------------------------------------------------------------------------
# global variables
nodes = {}
curr_node = 1
query = "INIT"
# -----------------------------------------------------------------------------
# string which is inside every testcase
test_start = '''
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/'''



# -----------------------------------------------------------------------------
# Sets the query variable
def createQuery():
    global query
    f = open(f"{raw_test_name}.apx.arg", "r")
    file_content = f.read().split('\n')
    query = file_content[0]
    f.close()


    
# -----------------------------------------------------------------------------
# Translates the attacks from .tgf format into .af format. It filles up the 
# dictionary nodes subsequently
def translateAttacks():
    global nodes
    global curr_node 

    f_inp = open(inp_file, "r")

    string_out = ""
    attacks = False
    for inp_line in f_inp:
        inp_line = inp_line.replace('\n', '')
        if inp_line == '#':
            attacks = True
            continue
        if attacks == False:
            nodes[inp_line] = curr_node
            curr_node += 1
            continue

        curr_line = inp_line.split()
        string_out = string_out + str(nodes[curr_line[0]]) + ' ' + str(nodes[curr_line[1]]) + '\n'
    
    f_inp.close()
    f_out = open(out_file, "w")
    f_out.write(f"p af {len(nodes)}\n")
    f_out.write(f"# FILE -> {inp_file}\n")
    f_out.write(f"# query -> {nodes[query]}\n")
    f_out.write(string_out)
    f_out.close()



# -----------------------------------------------------------------------------
# Saves the dictionary nodes in a mapping file x.dic
def saveDictionary():
    f_dic = open(dic_file, "w")
    temp = f"# Dictionary for {inp_file}"
    for node in nodes:
        temp = temp + "\n" + str(node) + " -> " + str(nodes[node])
    f_dic.write(temp)
    f_dic.close()



# -----------------------------------------------------------------------------
# Creates the Python tests for each DC-CO, DC-ST, DS-CO, DS-ST  
def createTests():
    f_mod = open(mod_inp_file, "r")
    attacks = list()
    for line in f_mod:
        curr_attack = ""
        if line[0] == '-':
            curr_attack += "s.del_attack("
        else:
            curr_attack += "s.add_attack("

        curr_nodes = line[line.find('(')+1 : line.find(')')].split(',')
        attacks.append(f"{curr_attack}{str(nodes[curr_nodes[0]])}, {str(nodes[curr_nodes[1]])})")
    f_mod.close()

    # each testcase gets its own file
    omega = ["DC", "DS"]
    sets = ["CO", "ST"]
    for o in omega:
        for s in sets:
            curr_file = f"{test_num}_{inp_file[:-4]}-{o}-{s}.py"
            f = open(curr_file, "w")
            f.write(f'{test_start}{out_file}")\n')
            f.write(f's = AFSolver("{s}", os.path.join(path, "{out_file}"))\n\n')
            f.write(f"for n in range(1, {len(nodes)+1}):\n\ts.add_argument(n)\n\n")

            query_D = "QUERY"
            if o == "DC":
                query_D = f"s.solve_cred([{nodes[query]}])"
            elif o == "DS":
                query_D = f"s.solve_skept([{nodes[query]}])"
            else:
                print("wrong cred/skept"); exit()

            f.write(f"{query_D}\n\n")
            for new_attack in attacks:
                f.write(f"{new_attack}\n")
                f.write(f"{query_D}\n\n")
            f.close()



# -----------------------------------------------------------------------------
# Creates the files, where the solutions are stated.
def createSolutions():
    omega = ["DC", "DS"]
    sets = ["CO", "ST"]
    for o in omega:
        for s in sets:
            curr_inp_file = open(f"instances-{raw_test_name}.apxm-{o}-{s}-D.out", "r")
            curr_out_file = open(f"{test_num}_{raw_test_name}-{o}-{s}.out", "w")

            inp_file = curr_inp_file.read().split('\n')
            for line in inp_file[1:]:
                curr_out_file.write(f"{line}\n")

            curr_out_file.close()
            curr_inp_file.close()



# -----------------------------------------------------------------------------
# Moves the files into the correct folders.
def moveToLocations():
    # destination folders
    dest_af = "../inputs/competition/"
    dest_storage = f"../inputs/competition/storage/{test_num}_{raw_test_name}"
    dest_tests = "tests/competition/"
    dest_solutions = "solutions/competition/"
    
    # input .af file
    shutil.move(out_file, dest_af)
    # storage files input
    os.mkdir(f"{dest_storage}")
    shutil.move(f"{raw_test_name}.tgf", dest_storage)
    shutil.move(f"{raw_test_name}.dic", dest_storage)
    shutil.move(f"{raw_test_name}.apx", dest_storage)
    shutil.move(f"{raw_test_name}.apxm", dest_storage)
    shutil.move(f"{raw_test_name}.apx.arg", dest_storage)
    #storage files output
    shutil.move(f"instances-{raw_test_name}.apxm-DC-CO-D.out", dest_storage)
    shutil.move(f"instances-{raw_test_name}.apxm-DC-ST-D.out", dest_storage)
    shutil.move(f"instances-{raw_test_name}.apxm-DS-CO-D.out", dest_storage)
    shutil.move(f"instances-{raw_test_name}.apxm-DS-ST-D.out", dest_storage)
    # tests
    shutil.move(f"{test_num}_{raw_test_name}-DC-CO.py", dest_tests)
    shutil.move(f"{test_num}_{raw_test_name}-DC-ST.py", dest_tests)
    shutil.move(f"{test_num}_{raw_test_name}-DS-CO.py", dest_tests)
    shutil.move(f"{test_num}_{raw_test_name}-DS-ST.py", dest_tests)
    # solutions
    shutil.move(f"{test_num}_{raw_test_name}-DC-CO.out", dest_solutions)
    shutil.move(f"{test_num}_{raw_test_name}-DC-ST.out", dest_solutions)
    shutil.move(f"{test_num}_{raw_test_name}-DS-CO.out", dest_solutions)
    shutil.move(f"{test_num}_{raw_test_name}-DS-ST.out", dest_solutions)



# -----------------------------------------------------------------------------
# Main function
def main():
    createQuery()
    translateAttacks()
    saveDictionary()
    createTests()
    createSolutions()
    moveToLocations()
# -----------------------------------------------------------------------------
# Main Guard
if __name__ == '__main__':
    main()