import networkx as nx
import numpy as np
import matplotlib.pyplot as plt

def show(data: dict):
    G = nx.DiGraph()
    edges = list()

    for line in data["R"]:
        edges.append( (line[0], line[1]) )

    fig = plt.figure()
    G.add_edges_from(edges)


    nx.draw(G, cmap = plt.get_cmap("jet"),
            edge_color="white", 
            node_size=5000, 
            with_labels=True, 
            arrowsize=50,
            linewidths=0.0,
            font_color="white",
            font_size=20,
            node_color="#8899aa")
    fig.set_facecolor("#00000F")
    plt.show()