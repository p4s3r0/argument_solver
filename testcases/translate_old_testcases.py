inp_file = "Medium-result-b1.tgf"
query = "a48_54"
out_file = inp_file[:-3] + "af"

nodes = {}
curr_node = 1

f_inp = open(inp_file, "r")
f_out = open(out_file, "w")

string_out = ""

attacks = False
for inp_line in f_inp:
    if inp_line == '#\n':
        attacks = True
        continue
    if attacks == False:
        continue

    curr_line = inp_line.replace('\n', '').split()

    if curr_line[0] not in nodes:
        nodes[curr_line[0]] = curr_node
        curr_node += 1
    if curr_line[1] not in nodes:
        nodes[curr_line[1]] = curr_node
        curr_node += 1

    string_out = string_out + str(nodes[curr_line[0]]) + ' ' + str(nodes[curr_line[1]]) + '\n'

f_out.write(f"p af {len(nodes)}\n")
f_out.write(f"# FILE -> {inp_file}\n")
f_out.write(f"# query -> {nodes[query]}\n")
f_out.write(string_out)

f_out.close()
f_inp.close()