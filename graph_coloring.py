from z3 import *
import sys
# STUDENTS: do not add or modify import statements!

# The parts that you should fill are marked with "INSERT YOUR CODE HERE".

# Colors are represented by numbers 0..nofColors-1.
# Nodes are supposed to be numbered continuously starting from 1

# For a node n, a Boolean variable hascol_n_c is true iff
# the node has been colored with color c.

def hascol(node, color):
    return Bool("hascol_%d_%d" % (node, color))


def exactlyOneFormula(formulas):
    if len(formulas) == 0: return False
    if len(formulas) == 1: return formulas[0]
    atLeastOne = Or(formulas)
    atLeastTwo = Or([And(f1,f2) for f1 in formulas for f2 in formulas if f2 is not f1])
    # Note: we have to use "is not" instead of "!=" above because
    # f2 != f1 would be a Z3 formula "f2 != f1" and here we want to check
    # whether f2 is not the same as f1
    return And(atLeastOne, Not(atLeastTwo))

# Every node is supposed to be colored with exactly one color

def oneColorFormula(node, nofColors):
    return exactlyOneFormula([hascol(node, color) for color in range(nofColors)])

# Make and return the coloring condition for an edge

def coloringConditionFormula(edge, nofColors):
    (n1, n2) = edge
    tempbool = True
    for c in range(nofColors):
        tempbool = And(tempbool, Not(And(hascol(n1, c), hascol(n2,c)))) 
    return tempbool

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

    def decodeColor(node):
      color = None
      for c in range(0, noc):
        var = hascol(node, c)
        cval = model[var]
        if cval == None:
          raise ValidationError( \
            "The model does not define the value of color_%d_%d properly!" \
            % (node, c))
        elif is_true(cval):
          if color == None:
            color = c 
          if color != c:
            raise ValidationError("Node %d has two colors %d and %d!" \
                                  % (node, color, c))
      return color

    colorof = [None for n in nodes] # Initialize

    # Check that each node is properly colored
    for n in nodes:
      c = decodeColor(n)
      if c == None:
        raise ValidationError( \
          "The model does not determine the color of node %d!" % (n))
      else:
        colorof[n-1] = c # Record

    # Other checks will be performed later

    return colorof
        
def extractNodes(edges):
    nodes = []
    for e in edges:
      (n1,n2) = e
      if n1 not in nodes: nodes.append(n1)
      if n2 not in nodes: nodes.append(n2)
    return nodes

def colorGraph(edges, nofColors, out = sys.stdout):
    assert(isinstance(nofColors, int) and nofColors >= 1)

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
    p("#colors: %d" % nofColors)

    # Create one solver instance that we'll use all the time
    s = Solver()

    for n in nodes:
      s.add(oneColorFormula(n, nofColors))

    for e in edges:
      s.add(coloringConditionFormula(e, nofColors))

    colors = []
    result = s.check()
    p("The solver says: "+str(result))

    if result == unsat:
      p("No coloring possible!")
      solution = "nonexistent"

    elif result == sat:
      model = s.model()
      colors = checkSolution(nodes, edges, nofColors, model)
      p("Colors for nodes: %s" % colors)
      solution = "found"

    else:
      assert(result == unknown)
      p('"unknown" (with reason "'+s.reason_unknown()+\
        '") returned by the solver, aborting!')
      solution = "error"

    return (solution,colors)
