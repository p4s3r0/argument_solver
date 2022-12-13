import argparse

import Parser
import Solver
import Visualize

# -----------------------------------------------------------------------------
# parses the arguments
# 
def argumentParser():
    parser = argparse.ArgumentParser(description="Parses a AF file into a dictionary")
    parser.add_argument("i", metavar="<input_file>", action="store", help="defines the input file ")
    parser.add_argument("-p", action="store_true", help="prints the parsed data", required=False)
    parser.add_argument("-c", action="store_true", help="prints the data in char format [a-z]", required=False)
    parser.add_argument("-g", action="store_true", help="Displays the graph", required=False)
    parser.add_argument("-s", action="store_true", help="prints the solutions", required=False)

    args = vars(parser.parse_args())
    file_name = args["i"]
    print_data = args["p"]
    display_graph = args["g"]
    show_solution = args["s"]
    char_format = args["c"]
    return file_name, print_data, char_format, display_graph, show_solution



def main():
    file_name, print_data, char_format, display_graph, show_solution = argumentParser()

    parser = Parser.parse(file_name, print_data, char_format)
    Solver.solve(parser.data, 
                 parser.all_nodes, 
                 parser.node_attacks, 
                 parser.node_defends,
                 show_solution,
                 char_format)

    if display_graph: Visualize.show(parser.data)

if __name__ == '__main__':
    main()