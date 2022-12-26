import Debug

# -----------------------------------------------------------------------------
class Parser: 
    def __init__(self):
        self.data = { "N": 0,
                      "R": list()}
        self.node_attacks = {}
        self.node_defends = {}
        self.all_nodes    = []

        

    # -----------------------------------------------------------------------------
    # processes the first "p" line of the input. 
    # @line -> first line of the input file
    def parseFirstLine(self, line: str) -> None:
        first_line = line.split(' ')
        if first_line[0] != 'p' or first_line[1] != "af":
            Debug.ERROR(f"ParseError: first line ('{line}') should have the format 'p af <N>'")
        self.data["N"] = int(first_line[2])
        


    # -----------------------------------------------------------------------------
    # parses one line of the input at stores it into the global data dictionary
    # @line -> current line which is being parsed
    def parseLine(self, line: str) -> None:
        line = line.replace('\n', '')
        curr_line = line.split(' ')
        if curr_line[0] == '#' or curr_line == '':
            return
        try:
            self.data["R"].append( [int(curr_line[0]), int(curr_line[1])] )
            if curr_line[0] not in self.node_attacks:
                self.node_attacks[curr_line[0]] = [int(curr_line[1])]
            else:
                self.node_attacks[curr_line[0]].append(int(curr_line[1]))
            if curr_line[1] not in self.node_defends:
                self.node_defends[curr_line[1]] = [int(curr_line[0])]
            else:
                self.node_defends[curr_line[1]].append(int(curr_line[0]))
            if curr_line[0] not in self.all_nodes: self.all_nodes.append(curr_line[0])
            if curr_line[1] not in self.all_nodes: self.all_nodes.append(curr_line[1])
        except:
            Debug.ERROR(f"ParserError: invalid line ('{line}') should have format '<i> <j>'")
        


    # -----------------------------------------------------------------------------
    # reads the input file and stores everything in the data object
    # @input_file -> input file name
    def readFile(self, input_file: str) -> None:
        f = open(input_file, "r")
        self.parseFirstLine(f.readline())
        for line in f:
            self.parseLine(line)
        f.close()



    # -----------------------------------------------------------------------------
    # prints the data in a structured way
    # @use_char_format -> use chars [a-z] instead of numbers [1-n]
    def printData(self, use_char_format: bool):
        Debug.INFO("PARSER", "Data begin\n")
        ASCII_OFFSET = 96
        Debug.INFO("OFFSET", f"N: {self.data['N']}")
        Debug.INFO("OFFSET", f"R: ")
        for rule in self.data['R']:
            if use_char_format:
                Debug.INFO("OFFSET", f"{chr(rule[0]+ASCII_OFFSET)} -> {chr(rule[1]+ASCII_OFFSET)}")
            else:
                Debug.INFO("OFFSET", f"{rule[0]} -> {rule[1]}")
        print()
        Debug.INFO("PARSER", "Data end")
        
            
            
            
# -----------------------------------------------------------------------------
# main function for parser. Creates the parser and starts it
# @input_file -> input file name
# @print_parser_data -> prints detailed parser informations
# @use_char_format -> use chars [a-z] instead of numbers [1-n]
def parse(input_file: str, print_parser_data: bool, use_char_format: bool):
    Debug.DEBUG("PARSER", f"started reading file {input_file}")
    parser = Parser()
    parser.readFile(input_file)
    if print_parser_data: parser.printData(use_char_format)
    Debug.DEBUG("PARSER", f"parsing done, found {len(parser.all_nodes)} nodes and {len(parser.data['R'])} edges")
    return parser


if __name__ == '__main__':
    Debug.ERROR("Parser.py should not be executed as main. Check the Readme.md")
    exit()