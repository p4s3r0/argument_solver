import os



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



passed_testcases = 0
def checkCorrectOutput(testcase: str, testcase_number: int):
    global passed_testcases
    solver_out_file = open("temp.txt", "r")
    solution_file = open(f"solutions/{testcase[:-3]}.out")

    solver_out = solver_out_file.read()
    solution_out = solution_file.read()

    solver_out_lines = [res[:2] for res in solver_out.split('\n') if res != '']
    solution_out_lines = [res[:2] for res in solution_out.split('\n') if res != '']



    if solver_out_lines == solution_out_lines:
        passed_testcases += 1
        print(f"{color.GREEN}PASSED{color.END}")
    else:
        print(f"{color.RED}FAILED{color.END}")
        print(f"got:\n{color.YELLOW}{solver_out}")
        print("------------------")
        print(f"{color.END}should be:\n{solution_out}")

    solution_file.close()
    solver_out_file.close()

    print(flush=True, end="")
    

    


def main():
    print(f"RUNNING { len(os.listdir('tests/competition')) } TESTCASES")
    testruns = 0
    for testcase in os.listdir("tests/competition"):
        print()
        print("################################################")
        print(f"{testruns+1}-TestCase [{testcase}]")
        os.system(f"python3 tests/competition/{testcase} > temp.txt")
        checkCorrectOutput("competition/" + testcase, testruns+1)
        print("################################################")
        testruns += 1

    print()
    print(f"{color.CYAN}{passed_testcases} PASSED and {testruns - passed_testcases} FAILED testcases{color.END}")
    print()
    os.remove("temp.txt")


if __name__ == "__main__":
    main()
