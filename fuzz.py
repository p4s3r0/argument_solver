"""
Copyright (c) 2023, Andreas Niskanen, University of Helsinki.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

import argparse, itertools, math, os, random, subprocess, sys, tempfile

# SET PATH TO REFERENCE SOLVER SUPPORTING ENUMERATION TASKS
REFERENCE_SOLVER = "./mu-toksia_static"

# IMPORT YOUR SOLVER
from Solver import AFSolver
# from mu_toksia import mu_toksia as AFSolver

def generate_random_af(n_args, prob_att, prob_sym, prob_self):
	args = set([i+1 for i in range(n_args)])
	atts = set()
	for s,t in itertools.combinations(args, 2):
		if random.random() < prob_att:
			if random.random() < prob_sym:
				atts.add((s,t))
				atts.add((t,s))
			else:
				if random.random() < 0.5:
					atts.add((s,t))
				else:
					atts.add((t,s))
	for a in args:
		if random.random() < prob_self:
			atts.add((a,a))
	return args, atts

def af_from_file(file, file_format):
	contents = file.read().split("\n")
	contents = [line.strip() for line in contents if len(line) > 0]
	if file_format == "p":
		p_line = [line for line in contents if line.startswith("p")]
		assert(len(p_line) == 1)
		p_line = p_line[0]
		n_args = int(p_line.replace("p af ", ""))
		args = set([i+1] for i in range(n_args))
		att_lines = [line for line in contents if not line.startswith("p") and not line.startswith("#")]
		atts = set()
		for line in att_lines:
			s,t = line.split()
			atts.add((s,t))
	elif file_format == "apx":
		arg_lines = [line for line in contents if line.startswith("arg")]
		args = set()
		arg_to_int = {}
		for i, line in enumerate(arg_lines):
			arg = line.replace("arg(", "").replace(").", "")
			arg_to_int[arg] = i+1
			args.add(i+1)
		att_lines = [line for line in contents if line.startswith("att")]
		atts = set()
		for line in att_lines:
			s,t = line.replace("att(", "").replace(").", "").split(",")
			atts.add((arg_to_int[s], arg_to_int[t]))
	elif file_format == "tgf":
		args = set()
		atts = set()
		arg_to_int = {}
		args_done = False
		for i, line in enumerate(contents):
			if line.strip == "#":
				args_done = True
				continue
			if not args_done:
				arg_to_int[line] = i+1
				args.add(i+1)
			else:
				s,t = line.split()
				atts.add((arg_to_int[s], arg_to_int[t]))
	else:
		print("Unknown file format:", file_format)
		sys.exit(1)
	return args, atts

def af_to_file(args, atts, file, file_format):
	if file_format == "p":
		file.write("p af " + str(len(args)) + "\n")
		for s,t in atts:
			file.write(str(s) + " " + str(t) + "\n")
	elif file_format == "apx":
		for a in args:
			file.write("arg(" + str(a) + ").\n")
		for s,t in atts:
			file.write("att(" + str(s) + "," + str(t) + ").\n")
	elif file_format == "tgf":
		for a in args:
			file.write(str(a) + "\n")
		file.write("#\n")
		for s,t in atts:
			file.write(str(s) + " " + str(t) + "\n")
	else:
		print("Unknown file format:", file_format)
		sys.exit(1)
	file.flush()

def enumerate_extensions(args, atts, semantics, file_format="apx"):
	if semantics == "ID":
		problem = "SE-ID"
	else:
		problem = "EE-" + semantics
	with tempfile.NamedTemporaryFile(mode="w", suffix="."+file_format) as tmp:
		af_to_file(args, atts, tmp, file_format)
		output = subprocess.check_output([REFERENCE_SOLVER, "-f", tmp.name, "-fo", file_format, "-p", problem]).decode("utf-8")
	output = "".join(output.split()) # remove all whitespace
	output = output.replace("],[", "][") # ICCMA'19: no commas between extensions
	if semantics != "ID":
		output = output[1:-1]
	if len(output) == 0:
		return []
	extension_strs = output[1:-1].split("][")
	extensions = []
	for string in extension_strs:
		if len(string) == 0:
			extensions.append([])
			continue
		str_split = string.split(",")
		ext = sorted(list(map(int, str_split)))
		extensions.append(ext)
	return extensions

def choose_action(actions, args, atts, args_remaining, atts_remaining):
	total_args = len(args) + len(args_remaining)
	total_elems = total_args + len(atts) + len(atts_remaining)
	w = [len(args_remaining), len(args), math.sqrt(len(atts_remaining)), math.sqrt(len(atts)), total_args, total_args]
	return random.choices(actions, weights=w, k=1)[0]

def add_argument(solver, args, atts, args_remaining, atts_remaining, trace=None):
	if len(args_remaining) == 0:
		return args, atts, args_remaining, atts_remaining
	arg = random.choice(list(args_remaining))
	args.add(arg)
	args_remaining.remove(arg)
	atts_remaining = atts_remaining | set((arg, another) for another in args)
	atts_remaining = atts_remaining | set((another, arg) for another in args)
	solver.add_argument(arg)
	if trace:
		trace.append(f"solver.add_argument({arg})")
	return args, atts, args_remaining, atts_remaining

def del_argument(solver, args, atts, args_remaining, atts_remaining, trace=None):
	if len(args) == 0:
		return args, atts, args_remaining, atts_remaining
	arg = random.choice(list(args))
	atts = atts - set((arg, another) for another in args)
	atts = atts - set((another, arg) for another in args)
	atts_remaining = atts_remaining - set((arg, another) for another in args)
	atts_remaining = atts_remaining - set((another, arg) for another in args)
	args.remove(arg)
	args_remaining.add(arg)
	solver.del_argument(arg)
	if trace:
		trace.append(f"solver.del_argument({arg})")
	return args, atts, args_remaining, atts_remaining

def add_attack(solver, args, atts, args_remaining, atts_remaining, trace=None):
	if len(atts_remaining) == 0:
		return args, atts, args_remaining, atts_remaining
	att = random.choice(list(atts_remaining))
	atts.add(att)
	atts_remaining.remove(att)
	s,t = att
	solver.add_attack(s,t)
	if trace:
		trace.append(f"solver.add_attack({s},{t})")
	return args, atts, args_remaining, atts_remaining

def del_attack(solver, args, atts, args_remaining, atts_remaining, trace=None):
	if len(atts) == 0:
		return args, atts, args_remaining, atts_remaining
	att = random.choice(list(atts))
	atts.remove(att)
	atts_remaining.add(att)
	s,t = att
	solver.del_attack(s,t)
	if trace:
		trace.append(f"solver.del_attack({s},{t})")
	return args, atts, args_remaining, atts_remaining

class colors:
    PASS = '\033[92m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'

def fail_and_exit(message, trace=None, initial_args=None, initial_atts=None):
	print(colors.FAIL + "FAIL" + colors.ENDC)
	print(message)
	if trace is not None:
		assert(initial_args is not None)
		assert(initial_atts is not None)
		print("Writing initial AF to error.af...")
		with open("error.af", "w") as file:
			af_to_file(initial_args, initial_atts, file, "p")
		print("Writing trace to error.py...")
		with open("error.py", "w") as file:
			file.write("# REPLACE THIS LINE WITH YOUR SOLVER IMPORT\n")
			file.write("\n")
			for line in trace:
				file.write(line + "\n")
		print("Exiting.")
	sys.exit(1)

if __name__ == "__main__":

	parser = argparse.ArgumentParser(description="ICCMA'23 Dynamic Track", formatter_class=argparse.ArgumentDefaultsHelpFormatter)
	parser.add_argument("--ref-format", choices=["p", "apx", "tgf"], default="apx", help="Input file format for reference solver")
	parser.add_argument("--min-args", type=int, default=10, help="Minimum number of arguments to generate")
	parser.add_argument("--max-args", type=int, default=50, help="Maximum number of arguments to generate")
	parser.add_argument("--prob-att", type=float, default=0.15, help="Probability of attack between two arguments")
	parser.add_argument("--prob-sym", type=float, default=0.05, help="Probability of attack being symmetric")
	parser.add_argument("--prob-self", type=float, default=0.01, help="Probability of self-attack")
	parser.add_argument("--prob-query", type=float, default=0.01, help="Probability of query")
	parser.add_argument("--initial-af", default=None, help="Initialize AF from this file")
	parser.add_argument("--initial-format", default="p", help="Initial AF file format")
	parser.add_argument("--semantics", default="CO,ST,PR", help="Comma-separated list of semantics to test")
	parser.add_argument("--tasks", default="DC,DS", help="Comma-separated list of reasoning tasks to test")
	parser.add_argument("--exclude", default="DC-PR,DS-CO", help="Comma-separated list of task-semantics combinations to exclude")
	parser.add_argument("--iterations", type=int, default=10, help="Number of test iterations")
	parser.add_argument("--ipafair-iterations", type=int, default=100, help="Number of IPAFAIR iterations")
	parser.add_argument("--mixed-query", action="store_true", help="Use non-singleton queries")
	parser.add_argument("--mixed-tasks", action="store_true", help="Use mixed credulous and skeptical solve calls")
	parser.add_argument("--verify-witness", action="store_true", help="Verify witness extension")
	parser.add_argument("--seed", type=int, default=None, help="Seed for random number generator")

	cmd_args = parser.parse_args()
	if cmd_args.seed is not None:
		random.seed(cmd_args.seed)

	if not os.path.exists(REFERENCE_SOLVER):
		fail_and_exit("Please set path to reference solver in the header of this script!")

	if not "AFSolver" in dir():
		fail_and_exit("Please import your solver in the header of this script!") 

	to_exclude = cmd_args.exclude.split(",")
	actions = ["ADD_ARG", "DEL_ARG", "ADD_ATT", "DEL_ATT", "SOLVE_CRED", "SOLVE_SKEPT"]

	i = 0
	while i < cmd_args.iterations:
		i = i+1
		if cmd_args.initial_af is None:
			args, atts = generate_random_af(random.randint(cmd_args.min_args, cmd_args.max_args), cmd_args.prob_att, cmd_args.prob_sym, cmd_args.prob_self)
		else:
			with open(cmd_args.initial_af, "r") as file:
				args, atts = af_from_file(file, cmd_args.initial_format)
		initial_args = list(args)
		initial_atts = list(atts)
		trace = []
		sigma = random.choice(cmd_args.semantics.split(","))
		assert(sigma in ["CO", "PR", "ST", "SST", "STG", "ID"])
		task = random.choice(cmd_args.tasks.split(","))
		assert(task in ["DC", "DS"])
		if task + "-" + sigma in to_exclude:
			i = i-1
			continue
		args_remaining = set(range(1, cmd_args.max_args+1)).difference(args)
		atts_remaining = set((s,t) for s in args for t in args).difference(atts)

		with tempfile.NamedTemporaryFile(mode="w", suffix=".af") as tmp:
			af_to_file(args, atts, tmp, "p")
			solver = AFSolver(sigma, tmp.name)
			trace.append(f'solver = AFSolver("{sigma}", "error.af")')

		for _ in range(cmd_args.ipafair_iterations):

			action = choose_action(actions, args, atts, args_remaining, atts_remaining)
			#print(action)
			if action == "ADD_ARG":
				args, atts, args_remaining, atts_remaining = add_argument(solver, args, atts, args_remaining, atts_remaining, trace)
			elif action == "DEL_ARG":
				args, atts, args_remaining, atts_remaining = del_argument(solver, args, atts, args_remaining, atts_remaining, trace)
			elif action == "ADD_ATT":
				args, atts, args_remaining, atts_remaining = add_attack(solver, args, atts, args_remaining, atts_remaining, trace)
			elif action == "DEL_ATT":
				args, atts, args_remaining, atts_remaining = del_attack(solver, args, atts, args_remaining, atts_remaining, trace)

			else: # solve

				if len(args) == 0:
					continue
				extensions = enumerate_extensions(args, atts, sigma)
				if not cmd_args.mixed_query:
					query_all = [random.choice(list(args))]
				else:
					query_all = [a for a in args if random.random() < cmd_args.prob_query]

				if (task == "DC" and not cmd_args.mixed_tasks) or (cmd_args.mixed_tasks and action == "SOLVE_CRED"):
					result = solver.solve_cred(query_all)
					trace.append(f"result = solver.solve_cred({query_all})")
					if result is True:
						if not any(all(query in extension for query in query_all) for extension in extensions):
							trace.append("assert(result is False)")
							fail_and_exit(print(f"Query {query_all} is not credulously accepted under {sigma}!"), trace, initial_args, initial_atts)
						if cmd_args.verify_witness:
							witness = sorted(solver.extract_witness())
							trace.append("witness = sorted(solver.extract_witness())")
							if not all(query in witness for query in query_all):
								fail_and_exit(print(f"Witness {witness} does not contain query {query_all}!"), trace, initial_args, initial_atts)
							if not any(witness == extension for extension in extensions):
								fail_and_exit(print(f"Witness {witness} does not an extension under {sigma}!"), trace, initial_args, initial_atts)
					elif result is False:
						if len(query_all) and any(all(query in extension for query in query_all) for extension in extensions):
							trace.append("assert(result is True)")
							fail_and_exit(f"Query {query_all} is credulously accepted under {sigma}!", trace, initial_args, initial_atts)
					else:
						fail_and_exit(f"Solver state is not OK!", trace, initial_args, initial_atts)

				elif (task == "DS" and not cmd_args.mixed_tasks) or (cmd_args.mixed_tasks and action == "SOLVE_SKEPT"):
					result = solver.solve_skept(query_all)
					trace.append(f"result = solver.solve_skept({query_all})")
					if result is True:
						if not all(all(query in extension for query in query_all) for extension in extensions):
							trace.append("assert(result is False)")
							fail_and_exit(f"Query {query_all} is not skeptically accepted under {sigma}!", trace, initial_args, initial_atts)
					elif result is False:
						if len(query_all) and all(all(query in extension for query in query_all) for extension in extensions):
							trace.append("assert(result is True)")
							fail_and_exit(f"Query {query_all} is skeptically accepted under {sigma}!", trace, initial_args, initial_atts)
						if cmd_args.verify_witness:
							witness = sorted(solver.extract_witness())
							trace.append("witness = sorted(solver.extract_witness())")
							if len(query_all) and all(query in witness for query in query_all):
								fail_and_exit(f"Witness {witness} contains query {query_all}!", trace, initial_args, initial_atts)
							if not any(witness == extension for extension in extensions):
								fail_and_exit(f"Witness {witness} is not an extension under {sigma}!", trace, initial_args, initial_atts)
					else:
						fail_and_exit(f"Solver state is not OK!", trace, initial_args, initial_atts)

				else:
					print("This should not happen!")
					sys.exit(1)

		print(colors.PASS + "PASS" + colors.ENDC, i, "/", cmd_args.iterations)