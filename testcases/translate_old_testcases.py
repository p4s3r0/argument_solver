inp_file = "Small-result-b2.tgf"
test_num = "3"
query = "a3_2"

out_file = inp_file[:-3] + "af"
dic_file = inp_file[:-3] + "dic"
mod_inp_file = inp_file[:-3] + "apxm"

nodes = {}
curr_node = 1


test_start = '''
import sys
sys.path.append('../../argument_solver')

from Solver import AFSolver
import os

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
    attacks = ""
    for line in f_mod:
        if line[0] == '-':
            attacks += "s.del_attack("
        else:
            attacks += "s.add_attack("

        curr_nodes = line[line.find('(')+1 : line.find(')')].split(',')
        attacks = attacks + str(nodes[curr_nodes[0]]) + ", " + str(nodes[curr_nodes[1]]) + ")\n"

    f_mod.close()
    omega = ["DC", "DS"]
    sets = ["CO", "ST"]

    for o in omega:
        for s in sets:
            curr_file = test_num + "_" + inp_file[:-4] + "-" + o + "-" + s + ".py"
            f = open(curr_file, "w")
            f.write(test_start)
            f.write(out_file)
            f.write('")\ns = AFSolver("')
            f.write(s)
            f.write('", os.path.join(path, "')
            f.write(out_file)
            f.write('"))\n\n')
            f.write(attacks)
            f.write("\n")
            f.write(f"for n in range(1, {len(nodes)+1}):\n\ts.add_argument(n)\n\n")
            if o == "DC":
                f.write(f"s.solve_cred([{nodes[query]}])")
            else:
                f.write(f"s.solve_skept([{nodes[query]}])")

            f.close()


def main():
    translateAttacks()
    saveDictionary()
    createTests()
    

if __name__ == '__main__':
    main()