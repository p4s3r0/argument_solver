import argparse


data = {
    "N": 0,
    "R": list()
}


# -----------------------------------------------------------------------------
# parses the arguments
# 
def argumentParser():
    parser = argparse.ArgumentParser(description="Parses a AF file into a dictionary")
    parser.add_argument("i", metavar="<input_file>", action="store", help="defines the input file ")
    parser.add_argument("-v", action="store_true", help="prints the parsed data", required=False)
    parser.add_argument("-vc", action="store_true", help="prints the parsed data in char format [a-z]", required=False)

    args = vars(parser.parse_args())
    file_name = args["i"]
    print_data = args["v"] or args["vc"]
    char_format = args["vc"]
    return file_name, print_data, char_format


# -----------------------------------------------------------------------------
# processes the first "p" line of the input. 
# @line -> first line of the input file
# @ERR -> if line does not have 'p af <N>' format
def parseFirstLine(line: str) -> None:
    first_line = line.split(' ')
    if first_line[0] != 'p' or first_line[1] != "af":
        print(f"[PARSE_ERROR]  first line ({line}) should have the format 'p af <N>'")
        exit()
    data["N"] = int(first_line[2])
        


# -----------------------------------------------------------------------------
# parses one line of the input at stores it into the global data dictionary
# @line -> current line which is being parsed
# @ERR -> if nodes are not ints
def parseLine(line: str) -> None:
    global data
    curr_line = line.split(' ')
    if curr_line[0] == '#' or curr_line == '\n':
        return
    try:
        data["R"].append( [int(curr_line[0]), int(curr_line[1])] )
    except:
        print("[PARSE_ERROR]  invalid line ({line}) should have format '<i> <j>'")
    


# -----------------------------------------------------------------------------
# reads the input file and stores everything in the data object
# @file_name -> name of the file from which should be read
def readFile(file_name: str) -> None:
    f = open(file_name, "r")
    parseFirstLine(f.readline())
    for line in f:
        parseLine(line)
    f.close()



# -----------------------------------------------------------------------------
# prints the data in a structured way
# @charFormat -> boolean variable if the nodes should be chars from a to z or numbers
def printData(charFormat: bool):
    ASCII_OFFSET = 96
    print(f"N: {data['N']}")
    print(f"------\nR: ")
    for rule in data['R']:
        if charFormat:
            print(f"{chr(rule[0]+ASCII_OFFSET)} -> {chr(rule[1]+ASCII_OFFSET)}")
        else:
            print(f"{rule[0]} -> {rule[1]}")
          
          
            
# -----------------------------------------------------------------------------
# main function for parser
def main():
    file_name, print_data, char_format = argumentParser()
    readFile(file_name)
    if print_data: printData(char_format)
    

if __name__ == "__main__":
    main()