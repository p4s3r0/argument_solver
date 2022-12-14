import Debug
# -----------------------------------------------------------------------------
# Parser class where we store the data
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
# @ERR -> if line does not have 'p af <N>' format
def parseFirstLine(p: Parser, line: str) -> None:
    first_line = line.split(' ')
    if first_line[0] != 'p' or first_line[1] != "af":
        Debug.ERROR(f"ParseError: first line ('{line}') should have the format 'p af <N>'")
    p.data["N"] = int(first_line[2])
        


# -----------------------------------------------------------------------------
# parses one line of the input at stores it into the global data dictionary
# @line -> current line which is being parsed
# @ERR -> if nodes are not ints
def parseLine(p: Parser, line: str) -> None:
    line = line.replace('\n', '')
    curr_line = line.split(' ')
    if curr_line[0] == '#' or curr_line == '':
        return
    try:
        p.data["R"].append( [int(curr_line[0]), int(curr_line[1])] )
        if curr_line[0] not in p.node_attacks:
            p.node_attacks[curr_line[0]] = [int(curr_line[1])]
        else:
            p.node_attacks[curr_line[0]].append(int(curr_line[1]))
        if curr_line[1] not in p.node_defends:
            p.node_defends[curr_line[1]] = [int(curr_line[0])]
        else:
            p.node_defends[curr_line[1]].append(int(curr_line[0]))
        if curr_line[0] not in p.all_nodes: p.all_nodes.append(curr_line[0])
        if curr_line[1] not in p.all_nodes: p.all_nodes.append(curr_line[1])
    except:
        Debug.ERROR(f"ParserError: invalid line ('{line}') should have format '<i> <j>'")
    


# -----------------------------------------------------------------------------
# reads the input file and stores everything in the data object
# @file_name -> name of the file from which should be read
def readFile(p: Parser, input_file: str) -> None:
    f = open(input_file, "r")
    parseFirstLine(p, f.readline())
    for line in f:
        parseLine(p, line)
    f.close()



# -----------------------------------------------------------------------------
# prints the data in a structured way
# @charFormat -> boolean variable if the nodes should be chars from a to z or numbers
def printData(p: Parser, charFormat: bool):
    Debug.INFO("PARSER", "Data begin\n")
    ASCII_OFFSET = 96
    Debug.INFO("OFFSET", f"N: {p.data['N']}")
    Debug.INFO("OFFSET", f"R: ")
    for rule in p.data['R']:
        if charFormat:
            Debug.INFO("OFFSET", f"{chr(rule[0]+ASCII_OFFSET)} -> {chr(rule[1]+ASCII_OFFSET)}")
        else:
            Debug.INFO("OFFSET", f"{rule[0]} -> {rule[1]}")
    print()
    Debug.INFO("PARSER", "Data end")
    
          
          
            
# -----------------------------------------------------------------------------
# main function for parser
def parse(input_file: str, print_parser_data: dict, use_char_format: bool):
    Debug.DEBUG("PARSER", f"started reading file {input_file}")
    p = Parser()
    readFile(p, input_file)
    if print_parser_data: printData(p, use_char_format)
    Debug.DEBUG("PARSER", f"parsing done, found {len(p.all_nodes)} nodes and {len(p.data['R'])} edges")

    return p


if __name__ == '__main__':
    Debug.ERROR("Parser.py should not be executed as main. Check the Readme.md")