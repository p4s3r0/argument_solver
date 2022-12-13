# Dependencies

We rely on the following python dependencies [`argparse`, `networkx`, `z3`]

## Installation

To install the dependencies use `pip` or `pip3`, depends on your configuration.

```bash
pip3 install argparse
pip3 install networkx
```

# Parser

<hr>

### Design
The **Parser** parses the input data and stores it into three dictionaries of the `Parser` class. The `data` dictionary stores how many Nodes there are and all the rules. The `node_attacks` dictionary stores for each node, which node is being attacked and the `nodee_defenses` stores fopr each node, from who he is being attacked. 

```python
data = {
    "N": 0,
    "R": list()
}
```

The `data` dictionary has two entries [`N`, `R`]. The entry `N` defines how many nodes there are. The entry `R` is a list of all vertices or attacks a node performs. The format is always:  
`a -> b` = `a` attacks `b` = `data["R"][i][0]` attacks `data["R"][i][1]`



### Arguments
The Arguments are parsed with the `argparse` module. We have 1 required argument (`input_file`) and 5 optional arguments (`-h`, `-p`, `-c`, `-g`, `-s`).  
The _required_ `input_file` argument defines the relative path to the input file  
The _optional_ `-h` argument shows the usage and argument description.  
The _optional_ `-v` argument prints the parsed data, where the Nodes are numbers from `1` to `N`  
The _optional_ `-c` argument prints the data, where the Nodes are characters from `a` to `z`. Not suited for `N > 26`.  
The _optional_ `-g` argument draws the graph.  
The _optional_ `-s` argument prints the solutions.  

