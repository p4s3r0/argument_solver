import argparse

import Parser
import Solver
import Visualize
import Debug

class Arguments:
    def __init__(self, input_file: str, print_parser_data: bool, show_graph: bool, show_solution: bool, use_char_format: bool, solution_amount: int, debug_mode: bool):
        self.input_file = input_file
        self.print_parser_data = print_parser_data
        self.show_graph = show_graph
        self.show_solution = show_solution
        self.use_char_format = use_char_format
        self.solution_amount = -1 if solution_amount == None else int(solution_amount)
        self.debug_mode = debug_mode



# -----------------------------------------------------------------------------
# parses the arguments
# 
def argumentParser():
    parser = argparse.ArgumentParser(description="Parses a AF file and calculates extensions")
    parser.add_argument("i", metavar="<input_file>", action="store", help="Defines the input file ")
    parser.add_argument("-p", action="store_true", help="Prints the parsed data", required=False)
    parser.add_argument("-c", action="store_true", help="Prints the data in char format [a-z]", required=False)
    parser.add_argument("-g", action="store_true", help="Displays the graph after execution", required=False)
    parser.add_argument("-s", action="store_true", help="Prints all solutions in set format", required=False)
    parser.add_argument("-d", action="store_true", help="Activate Debug mode", required=False)
    parser.add_argument("-k", action="store", help="Define the amount of solutions", required=False)

    arguments = vars(parser.parse_args())
    args = Arguments(arguments["i"], 
                     arguments["p"], 
                     arguments["g"], 
                     arguments["s"], 
                     arguments["c"], 
                     arguments["k"], 
                     arguments["d"])
    return args



def main():
    Debug.INFO("INFO", "Starting program\n")
    args = argumentParser()

    Debug.initDebug(args.debug_mode, args.print_parser_data, args.show_solution)

    parser = Parser.parse(args.input_file, args.print_parser_data, args.use_char_format)
    solver = Solver.solve(parser, args.solution_amount, args.show_solution, args.use_char_format)

    if args.show_graph: Visualize.show(parser.data, args.use_char_format)
    
    Debug.INFO("INFO", "Ending Program\n")



if __name__ == '__main__':
    main()