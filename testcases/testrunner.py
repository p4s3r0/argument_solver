# -----------------------------------------------------------------------------
# TESTRUNNER_SMALL.PY
# This testrunner is used to run the competition tests. The competition tests
# are the testcases, which were used in the previous competition with the
# public solutions. The testcases were translated with the 
# "translate_old_testcases.py" script.
# -----------------------------------------------------------------------------
import os
import itertools
import threading
import time
import sys



# color class for printing
class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   UNDERLINE = '\033[4m'
   BOLD = '\033[1m'
   END = '\033[0m'



# -----------------------------------------------------------------------------
# Checks if we got the correct output. If yes, print PASSED if not, print FAILED
# and show what we got and what the solution is
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
        print(f"\r{color.GREEN}PASSED           {color.END}")
    else:
        print(f"\r{color.RED}FAILED             {color.END}")
        print(f"got:\n{color.YELLOW}{solver_out}")
        print("------------------")
        print(f"{color.END}should be:\n{solution_out}")

    solution_file.close()
    solver_out_file.close()

    print(flush=True, end="")
    


# -----------------------------------------------------------------------------
# Function for calculating animation
testcase_finished = False
def animate():
    c1 = [c for c in "◢ ◣ ◤ ◥".split(" ")]
    c2 = [c for c in ["⢿⣿", "⣻⣿", "⣽⣿", "⣾⣿", "⣷⣿", "⣿⣾", "⣿⣷", "⣿⣯", "⣿⣟", "⣿⡿", "⣿⢿", "⡿⣿"]]
    c3 = [c for c in ["⠧⠇", "⠯⠆", "⠯⠅", "⠯⠃", "⠏⠇", "⠫⠇", "⠭⠇", "⠮⠇"]]
    for c in itertools.cycle(c3):
        if testcase_finished:
            sys.exit()
        sys.stdout.write(f"\r{color.YELLOW}CALCULATING {c}")
        sys.stdout.flush()
        time.sleep(0.4)



# -----------------------------------------------------------------------------
# Main function of the program
def main():
    global testcase_finished
    total_time_start = time.time()
    print(f"RUNNING { len(os.listdir('tests/competition')) } TESTCASES")
    testruns = 0
    for testcase in os.listdir("tests/competition"):
        testcase_finished = False
        print()
        print("################################################")
        print(f"{testruns+1}-TestCase [{testcase}]")

        t = threading.Thread(target=animate)
        t.start()

        start = time.time()
        os.system(f"python3 tests/competition/{testcase} > temp.txt")
        end = time.time()
        testcase_finished = True
        checkCorrectOutput("competition/" + testcase, testruns+1)
        print(f"Time: {color.BOLD}{str(round(end - start, 2))}{color.END}s")
        print("################################################")
        testruns += 1
    total_time_end = time.time()

    print(f"\n{color.CYAN}{passed_testcases} PASSED and {testruns - passed_testcases} FAILED testcases{color.END}")
    print(f"Time for all Testcases: {color.BOLD}{str(round(total_time_end - total_time_start, 2))}{color.END}s")
    os.remove("temp.txt")



# -----------------------------------------------------------------------------
# Main Guard
if __name__ == "__main__":
    main()
