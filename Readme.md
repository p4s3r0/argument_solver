# Execution
If you want to use the standalone version, switch to the `standalone` branch!

To execute the project, we recommend using a Python Virtual Environment. With the virtual environment installed (check [Installation](#-Installation)), create a new environment and activate it. After setting it up, install the dependencies recursivly:

```bash
python3 -m venv venv/
source venv/bin/activate
pip3 install -r requirements.txt
```

### Arguments
The Arguments are parsed with the `argparse` module. We have a required argument (`input_file`) and optional arguments (`-h`, `-p`, `-c`, `-g`, `-s`, `-d`, `-k`).  

The _required_ `input_file` argument defines the relative path to the input file  
The _optional_ `-h` argument shows the usage and argument description.  
The _optional_ `-v` argument prints the parsed data, where the Nodes are numbers from `1` to `N`  
The _optional_ `-c` argument prints the data, where the Nodes are characters from `a` to `z`. Not suited for `N > 26`.  
The _optional_ `-g` argument draws the graph.  
The _optional_ `-s` argument prints the solutions.  
The _optional_ `-d` activates the debug mode.  
The _optional_ `-k` defines the amount of solutions the solver should find.
  
<hr>

# Dependencies

If you want to execute with the virtual environment you need to install `venv` for python. If not, feel free to skip it.
## Installation
For the virtual environment you need to install the `python3.8-venv` package.

```bash
sudo apt install python3.8-venv
```

To install the python dependencies use `pip` or `pip3`, depends on your configuration. 

```bash
pip3 install -r requirements.txt
```

<hr>

# Parser


### Design
The **Parser** parses the input data and stores it into three dictionaries of the `Parser` class. The `data` dictionary stores how many Nodes there are and all the rules. The `node_attacks` dictionary stores for each node, which node is being attacked and the `nodee_defends` stores fopr each node, from who he is being attacked. 

```python
data = {
    "N": 0,
    "R": list()
}
```

The `data` dictionary has two entries [`N`, `R`]. The entry `N` defines how many nodes there are. The entry `R` is a list of all vertices or attacks a node performs. The format is always:  
`a -> b` = `a` attacks `b` = `data["R"][i][0]` attacks `data["R"][i][1]`
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

##### <ins>Admissible Set</ins>
The admissible Sets are computed with the formula:

$$ \bigwedge_{a \in A} \big( \big( a \rightarrow  \bigwedge_{b:(b, a) \in R} \lnot b \big) \land \big( a \rightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$

##### <ins>Preferred Set of k Solutions</ins>
The preferred Sets are the maximal model of the formula:

$$ \bigwedge_{a \in A} \big( \big( a \rightarrow  \bigwedge_{b:(b, a) \in R} \lnot b \big) \land \big( a \rightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$

##### <ins>Grounded extensions of k Solutions</ins>
The grounded Sets are the minimal model of the formula:

$$ \bigwedge_{a \in A} \big( \big( a \rightarrow  \bigwedge_{b:(b, a) \in R} \lnot b \big) \land \big( a \leftrightarrow \bigwedge_{b:(b,a) \in R} \big( \bigvee_{c:(c,b) \in R} c\big) \big)\big)$$
<hr>

# Time Tracker

**Sum** $\rightarrow$ **126** hours

**[13.10.2022]** $\rightarrow$ **5**h _Project definition with some research_

**[01.11.2022]** $\rightarrow$ **8**h _Researching on mini sat extensions for diverse solution SAT-Solver_

**[12.11.2022]** $\rightarrow$ **5**h _Researching on the topic_

**[30.11.2022]** $\rightarrow$ **2**h _Clearifiyng the exact topic of the project_

**[07.12.2022]** $\rightarrow$ **10**h _Created Parser for AF programs_

**[09.12.2022]** $\rightarrow$ **6**h _Added Arguments to Parser and set up github repository_

**[10.12.2022]** $\rightarrow$ **10**h _Started with implementing The SAT-Solver framework and did some research on stable solution_

**[11.12.2022]** $\rightarrow$ **9**h _Added stable solution calculation and researched on complete solution_

**[11.12.2022]** $\rightarrow$ **5**h _Added complete solution calculation_

**[14.12.2022]** $\rightarrow$ **8**h _Added more arguments, changed code structure and added improved debugging mechanism_

**[27.12.2022]** $\rightarrow$ **3**h _Refactored code for better readability_

**[09.01.2023]** $\rightarrow$ **4**h _Problem Solving with Supervisor, fixed admissible and complete set_

**[06.02.2023]** $\rightarrow$ **4**h _Added preferred and grounded set calculation_

**[07.02.2023]** $\rightarrow$ **1**h _Talk with Supervisor about competition and implementation Details_

**[09.02.2023]** $\rightarrow$ **5**h _Changed structure to support the ipafair API_

**[10.02.2023]** $\rightarrow$ **8**h _Changing stuff to support adding arguments and deleting arguments_

**[12.02.2023]** $\rightarrow$ **7**h _Added checks if set is still admissible or stable_

**[13.02.2023]** $\rightarrow$ **8**h _Added check if set is still preferred and applied check when solving for credulous_

**[14.02.2023]** $\rightarrow$ **10**h _Credulous and Skeptical can now be computed, with previous solution check (+ validation) and testrunner + tests added_

**[15.02.2023]** $\rightarrow$ **8**h _Extracted and Translated old competition testcases and added second Testrunner for Competition_





