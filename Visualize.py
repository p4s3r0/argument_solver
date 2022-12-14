# create the graph
import networkx as nx
import numpy as np
# plot the graph
import matplotlib.pyplot as plt
# setting seed to not randomize the graph drawing
import random
import numpy as np
seed = 33
random.seed(seed)


def show(data: dict, use_char_format: bool):
    ASCII_OFFSET = 96
    np.random.seed(seed)
    G = nx.DiGraph()
    edges = list()

    for line in data["R"]:
        if use_char_format:
            edges.append( (chr(line[0]+ASCII_OFFSET), chr(line[1]+ASCII_OFFSET)) )
        else:
            edges.append( (line[0], line[1]) )


    fig = plt.figure()
    G.add_edges_from(edges)


    nx.draw(G,
            edge_color="white", 
            width=3,
            node_size=5000, 
            with_labels=True, 
            arrowsize=50,
            linewidths=0.0,
            font_color="white",
            font_size=20,
            node_color="#8899dd",
            connectionstyle='arc3, rad = 0.07')
    fig.set_facecolor("#222222")
    plt.show()