# Dependencies

All dependencies are pre downloaded into the `libraries` folder. In order to install them, `pip` needs to be installed at the target system. Then simply execute the following command. 

```bash
pip3 install --no-index --find-links libraries -r requirements.txt
```

# Example Test Program

Place the example test into the main directory.

```python
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