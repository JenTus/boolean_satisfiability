from z3 import *
import sys
# STUDENTS: do not add or modify import statements!

# The parts that you should fill are marked with "INSERT YOUR CODE HERE".

# Cliques are represented by numbers 0..nofCliques-1.

# The graph is undirected but the edges are represented
# as pairs (n1,n2) where n1<n2 for the sake of compactness

# For a node n, a Boolean variable member_n_c is true iff
# the node is belongs to a clique c. A node can belong to
# several cliques simultaneously.

def member(node, clique):
    return Bool("member_%d_%d" % (node, clique))

# Each clique must contain at least one node

def assignNodesFormula(nodes, clique):
    return Or([member(n, clique) for n in nodes]) # INSERT YOUR CODE HERE

# In a clique, every pair of nodes must be connected by an edge

def testCompletenessFormula(clique, nodes, edges):
    tempbool = True
    for i in range(len(nodes)):
        for j in range(i+1, len(nodes)):
            if (nodes[i],nodes[j]) not in edges:
                tempbool = And(tempbool,Or(Not(member(nodes[i], clique)), Not(member(nodes[j], clique))))
    return tempbool # INSERT YOUR CODE HERE

# Cliques must NOT be contained in each other

#cliqe1 not in clique 2
def testInclusionFormula(clique1, clique2, nodes):
    tempbool = True
    for node in nodes:
        tempbool = And(tempbool, Or(Not(member(node, clique1)), member(node, clique2)))
    return Not(tempbool) # INSERT YOUR CODE HERE

# A clique is a maximal set of nodes such that every pair of nodes
# in it is connected by and edge.

def testMaximalityFormula(clique, nodes, edges):
    tempbool = False
    for i in nodes: 
        nei = []
        for j in edges:
            if i in j:
                nei.extend([j[0],j[1]])
        nei = list(set(nei)) #contain i 
        notnei = list(set(nodes) - set(nei)) #all not neighbors
        nei.remove(i)#neighbors not contain i
        
        tempbool = Or(tempbool, And(Not(member(i, clique)), Or([member(node, clique) for node in nei]), And([Not(member(node, clique)) for node in notnei])))
    return Not(tempbool) # INSERT YOUR CODE HERE

# Each edge must be contained in at least one clique
def coverEdgeFormula(edge, nofCliques):
    (n1,n2) = edge
    return Or([And(member(n1,clique),member(n2,clique)) for clique in range(0, nofCliques)])

class ValidationError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def checkSolution(nodes, edges, noc, model, out = sys.stdout):
    """
    Print (and validate) the solution found 
    """
    assert(isinstance(noc, int) and noc >= 1)

    # Helper functions
    def p(txt):
        if(out): out.write(txt+"\n")

    def decodeClique(clique):
        members = []
        for n in nodes:
            var = member(n, clique)
            val = model[var]
            if val == None:
                raise ValidationError("The model does not define the value of member_%d_%d properly!" % (n, clique))
            elif is_true(val):
                members.append(n)
        return members

    allcliques = []

    for c in range(0, noc):
        cnodes = decodeClique(c)
        if cnodes == None:
            raise ValidationError( \
                "The model does not determine the clique %d!" % (c))
        else:
            allcliques.append(cnodes)

    # Check that each clique is non-empty
    for c in range(0, noc):
        if allcliques[c] == []:
            raise ValidationError("Clique %d is empty!" % (c))

    # Other checks are perfomed later

    return allcliques
        
def extractNodes(edges):
    nodes = []
    for e in edges:
      (n1,n2) = e
      assert(isinstance(n1, int) and isinstance(n2, int) and n1 < n2)
      if n1 not in nodes: nodes.append(n1)
      if n2 not in nodes: nodes.append(n2)
    return nodes

def findCliques(edges, nofCliques, out = sys.stdout):
    assert(isinstance(nofCliques, int) and nofCliques >= 1)

    nofEdges = len(edges)
    assert(nofEdges >= 1)

    nodes = extractNodes(edges)
    nofNodes = len(nodes)

    # Helper functions
    def p(txt):
        if out: out.write(txt+'\n')
    def pr(txt):
        if out: out.write(txt)

    solution = None
    p("---")
    p("%d nodes: %s" % (nofNodes,nodes))
    p("%d edges: %s" % (nofEdges,edges))
    p("#cliques: %d" % nofCliques)

    # Create one solver instance that we'll use all the time
    s = Solver()

    for c in range(0, nofCliques):
        s.add(assignNodesFormula(nodes, c))

    for c in range(0, nofCliques):
        s.add(testCompletenessFormula(c, nodes, edges))

    for c1 in range(0, nofCliques):
        for c2 in range(c1+1, nofCliques):
            s.add(testInclusionFormula(c1,c2,nodes))
            s.add(testInclusionFormula(c2,c1,nodes))

    for c in range(0, nofCliques):
        s.add(testMaximalityFormula(c, nodes, edges))

    for e in edges:
        s.add(coverEdgeFormula(e, nofCliques))
 
    cliques = []
    result = s.check()
    p("The solver says: "+str(result))

    if result == unsat:
        p("No coverage possible!")
        solution = "nonexistent"

    elif result == sat:
        model = s.model()
        cliques = checkSolution(nodes, edges, nofCliques, model)
        p("Cliques of the graph: %s" % cliques)
        solution = "found"

    else:
        assert(result == unknown)
        p('"unknown" (with reason "'+ \
          s.reason_unknown()+ \
          '") returned by the solver, aborting!')
        solution = "error"

    return (solution,cliques)
