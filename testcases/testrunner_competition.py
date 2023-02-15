import os

testcases = [
    "competition/1_Medium-result-b1-DC-CO.py",
    "competition/1_Medium-result-b1-DC-ST.py",
    "competition/1_Medium-result-b1-DS-CO.py",
    "competition/1_Medium-result-b1-DS-ST.py",
]


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
    solution_file = open(f"solutions/{testcase[:-3]}.sol")

    solver_out = solver_out_file.read()
    solution_out = solution_file.read()

    if solver_out[:2] == solution_out[:2]:
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
    





print(f"RUNNING {len(testcases)} TESTCASES")
for i, testcase in enumerate(testcases):
    print()
    print("################################################")
    print(f"{i+1}-TestCase [{testcase}]")
    os.system(f"python3 tests/{testcase} > temp.txt")
    checkCorrectOutput(testcase, i+1)
    print("################################################")

print()
print(f"{color.CYAN}{passed_testcases} PASSED and {len(testcases) - passed_testcases} FAILED testcases{color.END}")
print()

os.remove("temp.txt")
