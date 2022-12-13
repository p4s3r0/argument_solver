import Parser
import Solver
import Visualize

def main():
    data, all_nodes, node_attacks, node_defends = Parser.parse()
    Solver.solve(data, all_nodes, node_attacks, node_defends)
    #Visualize.show(data)

if __name__ == '__main__':
    main()