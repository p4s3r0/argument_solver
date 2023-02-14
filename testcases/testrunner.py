import os

testcases = [
    "1_test_complete_cred_no_assumption.py",  
    "2_test_complete_cred_one_assumption.py", 
    "3_test_complete_cred_one_assumption.py", 
    "4_test_complete_cred_two_assumptions.py",
    "5_test_complete_cred_two_assumptions.py",
    "6_test_complete_cred_add_argument.py",
    "7_test_complete_cred_del_argument.py",
    "8_test_complete_cred_add_attack.py",
    "9_test_complete_cred_del_attack.py",
    "10_test_complete_skept_no_assumption.py",  
    "11_test_complete_skept_one_assumption.py", 
    "12_test_complete_skept_one_assumption.py", 
    "13_test_complete_skept_two_assumptions.py", 
    "14_test_complete_skept_two_assumptions.py", 
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

    if solver_out == solution_out:
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
