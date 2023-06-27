# -----------------------------------------------------------------------------
# PARSER.PY
# Parses a .af File and sets everything up for the Solver
# -----------------------------------------------------------------------------
import Exceptions as Exception
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
            raise Exception.ParseError
        self.data["N"] = int(first_line[2])
        for i in range(0, int(first_line[2])):
            self.all_nodes.append(str(i+1))
        


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
            raise Exception.ParseError

        

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
# main function for parser. Creates the parser and starts it
# @input_file -> input file name
def parse(input_file: str):
    parser = Parser()
    if input_file == None: return parser
    parser.readFile(input_file)
    return parser



# -----------------------------------------------------------------------------
# Main Guard
if __name__ == '__main__':
    raise Exception.LibraryWasRunAsMain
