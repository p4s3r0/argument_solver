
debug_mode = False
print_parser_data = False
show_solution = False
production_mode = True

def initDebug(debug_mode_arg: bool, print_parser_data_arg: bool, show_solution_arg: bool):
    global debug_mode, print_parser_data, show_solution
    debug_mode, print_parser_data, show_solution = debug_mode_arg, print_parser_data_arg, show_solution_arg



class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   UNDERLINE = '\033[4m'
   END = '\033[0m'



def printSolver(message: str):
    print(f"{color.GREEN}[SOLVER]{color.END}  {message}")



def printInfo(message: str):
    print(f"{color.BLUE}[MAIN  ]{color.END}  {message}", end="")


 
def printParser(message: str):
    print(f"{color.PURPLE}[PARSER]{color.END}  {message}")



def printError(message: str):
    print(f"{color.RED}[ERROR ]{color.END}  {message}")



def printOffset(message):
    print(f"          {message}")



def INFO(type: str, message: str):
    if production_mode: return
    if type == "SOLVER" and show_solution:
        printSolver(message)
    elif type == "PARSER" and print_parser_data:
        printParser(message)
    elif type == "INFO":
        printInfo(message)
    elif type == "OFFSET":
        printOffset(message)



def DEBUG(type: str, message: str):
    if production_mode: return
    if not debug_mode:
        return
    if type == "SOLVER":
        printSolver(message)
    elif type == "INFO":
        printInfo(message)
    elif type == "PARSER":
        printParser(message)
    elif type == "OFFSET":
        printOffset(message)
    else:
        print(f"'{type}' IS WRONG KEY FOR DEBUG DEBUG")

def ERROR(message: str):
    printError(message)
    exit()
