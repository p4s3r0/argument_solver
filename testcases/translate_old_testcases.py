inp_file = "A-1-admbuster_1000.tgf"
test_num = "2"
query = "c50"

out_file = test_num + "_" + inp_file[:-3] + "af"
dic_file = inp_file[:-3] + "dic"
mod_inp_file = inp_file[:-3] + "apxm"

nodes = {}
curr_node = 1


test_start = '''
import sys
import os
sys.path.append('../../argument_solver')

from Solver import AFSolver

path = os.path.dirname("../../argument_solver/inputs/competition/'''




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



def saveDictionary():
    f_dic = open(dic_file, "w")
    temp = f"# Dictionary for {inp_file}"
    for node in nodes:
        temp = temp + "\n" + str(node) + " -> " + str(nodes[node])
    f_dic.write(temp)
    f_dic.close()



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


def main():
    translateAttacks()
    saveDictionary()
    createTests()
    

if __name__ == '__main__':
    main()