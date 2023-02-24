# Execution
If you want to use the standalone version, switch to the `standalone` branch! If you want to test the implementation with output to `stdout`. switch to `dev` branch!

To execute the project, we recommend using a Python Virtual Environment (check [Installation](#-Installation)). After activating the virtual environment or if you decide to don't use it, install the libraries with the following command:

```bash
pip3 install -r requirements.txt
```

After installation, simply place a test program in the main directory and execute it with 

```bash
python3 <name>.py
```
<hr>

## Example Test Program
```python3
from Solver import AFSolver

s = AFSolver("CO", None)

s.add_argument(1)
s.add_argument(2)
s.add_attack(1, 2)

assert(s.solve_cred([1]))
assert(not s.solve_cred([2]))

s.del_attack(1,2)
assert(s.solve_cred([1]))
assert(s.solve_cred([2]))

s.add_argument(3)
s.add_attack(3, 2)
s.add_attack(2, 1)
assert(s.solve_cred([1]))
assert(not s.solve_cred([2]))
assert(s.solve_cred([3]))

s.del_argument(1)
s.add_argument(4)
s.add_attack(4, 3)
s.add_attack(3, 4)
assert(s.solve_cred([2]))
assert(s.solve_cred([3]))
assert(not s.solve_skept([4]))
```

<hr>

# Dependencies

If you want to execute with the virtual environment you need to install `venv` for python. If not, feel free to skip it.
## Installation
For the virtual environment you need to install the `python3.8-venv` package, create a virtual environment and activate it.

```bash
sudo apt install python3.10-venv
python3 -m venv venv/
source venv/bin/activate
```

To install the python dependencies use `pip` or `pip3`, depends on your configuration. 

```bash
pip3 install -r requirements.txt
```

<hr>


# Solver


### Purpose
The **Solver** is implemented in python with the `z3` module. It produces k solutions for the argumentation model problem and [TODO: needs extension].
### Solutions
##### <ins>Stable extensions</ins>
The stable extensions are computed with the formula:

$$ \bigwedge_{a \in A} \big( a \leftrightarrow  \bigwedge_{b:(b, a) \in R} \lnot b \big) $$

##### <ins>Complete extensions</ins>
The complete extensions are computed with the formula:

$$ \bigwedge_{a \in A} \big( \big( a \rightarrow  \bigwedge_{b:(b, a) \in R} \lnot b \big) \land \big( a \leftrightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$

<hr>






