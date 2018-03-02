from z3 import *
import sys
# STUDENTS: do not add or modify import statements!

#
# Some auxiliary functions are defined first, it is probably a good idea
# to have a look on them, too.
# The parts that you should fill are marked with "INSERT YOUR CODE HERE".
#

#
# Return a formula that evaluates to true if and only if
# exactly one of the argument formulas evaluates to true.
# This is a straightforward, quadratic construction; better ones do exist.
#
def exactlyOneFormula(formulas):
    if len(formulas) == 0: return False
    if len(formulas) == 1: return formulas[0]
    atLeastOne = Or(formulas)
    atLeastTwo = Or([And(f1,f2) for f1 in formulas for f2 in formulas if f2 is not f1])
    # Note: we have to use "is not" instead of "!=" above because
    # f2 != f1 would be a Z3 formula "f2 != f1" and here we want to check
    # whether f2 is not the same as f1
    return And(atLeastOne, Not(atLeastTwo))


# States of the game guessed to be reachable are
# represented for node v with a Boolean variable
# "S_n"

def sv(v):
    return Bool("S_%d" % (v))

# The strategy of Eloise and all outgoing edges of Abelard
# will be represented for each edge (v,w) with predicate
# "T_v_w"

def tvw(v, w):
    return Bool("T_%d_%d" % (v,w))

# The integer variables "x_v" are needed for each
# node v to check that no loop in the game is
# won by Abelard

def xv(v):
    return Int("x_%d" % (v))


# The initial node must be in the game

def forceInitialNode(initialNode):
    return sv(initialNode)

# Eloise should guess exactly one outgoing edge for
# each guessed to be reachable eNode

def guessEloiseStrategy(eNodes, nodeOutEdges):
    guesses = []
    for v in eNodes:
        out = nodeOutEdges[v]
        outsv = [tvw(v,w) for w in out]
        guesses.append(Implies(sv(v),exactlyOneFormula(outsv)))
    return And(guesses)


# Abelard nodes that have been guessed to be reachable
# will force also all their outgoing edges to be reachable

def forceAbelardSuccessors(aNodes, nodeOutEdges):
    guesses = []
    for v in aNodes:
        out = nodeOutEdges[v]
        outsv = [tvw(v,w) for w in out]
        guesses.append(Implies(sv(v), And([o for o in outsv]))) #not sure, means all the out-paths are possible, and seems to be unreasonable
        guesses.append(Implies(Not(sv(v)), And([Not(o) for o in outsv])))
    return And(guesses)

# Force nodes with guessed reachable incoming edges
# to also be guessed to be reachable

def forceNodesWithIncomingEdges(nodes, nodeInEdges):
    guesses = []
    for w in nodes:
        inn = nodeInEdges[w]
        innsv = [tvw(v,w) for v in inn]
        guesses.append(Implies(Or(innsv), sv(w))) 
    return And(guesses) # INSERT YOUR CODE HERE


# Remove all models which contain a guessed to be reachable
# loop consisting of only nodes with priority 1

def removeAbelardWins(omega, edges):
    removes = []
    for e in edges:
        (v, w) = e
        removes.append(Implies(And(omega[v] == 1, omega[w] == 1, tvw(v,w)), xv(v) < xv(w)))
    return And(removes)


# An exception thrown when a model is not consistent with the problem statement

class ValidationError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

# Checking code to ensure the found model is a valid games strategy with which Eloise can win
    
def checkSolution(edges, initialNode, nodes, eNodes, aNodes, omega, 
                  nodeOutEdges, nodeInEdges, model, out = sys.stdout):
    """
    Print (and validate) the solution found 
    """

    # Helper functions
    def p(txt):
        if(out): out.write(txt+"\n")

    # Decode guessed reachable node vars
    def decodeSv(nodes, model):
        guessedReachableStates = []
        for n in nodes:
            var = sv(n)
            val = model[var]
            if val == None:
                raise ValidationError("The model does not define the value of S_%d properly!" % (n))
            elif is_true(val):
                guessedReachableStates.append(n)
        return guessedReachableStates

    # Decode guessed reachable edge vars
    def decodeTvw(edges, model):
        guessedReachableEdges = []
        for e in edges:
            (v, w) = e
            var = tvw(v,w)
            val = model[var]
            if val == None:
                raise ValidationError("The model does not define the value of T_%d_%d properly!" % (v,w))
            elif is_true(val):
                guessedReachableEdges.append(e)
        return guessedReachableEdges

    
    # Recursively check for a loop where Abelard wins - very non-optimal for large game graphs
    
    def goalReachableUsingPriorityOneNodesOnly(omega, nodeOutEdges, decodedSv, 
                                               decodedTvw, startNode, goalNode, seenNodes):
        assert(omega[startNode] == 1)
        assert(startNode in decodedSv)

        #        print startNode, goalNode, seenNodes
        
        if (startNode in seenNodes):
            return
        
        seenNodes.append(startNode)

        for w in nodeOutEdges[startNode]:
            
            if (omega[w] != 1):
                continue
            if (w not in decodedSv):
                continue
            if ([startNode, w] not in decodedTvw):
                continue

            if (w == goalNode):
                raise ValidationError("A loop won by Abelard found that goes through node %d and only uses guessed to be reachable nodes with priority 1!" % (goalNode))
           
            goalReachableUsingPriorityOneNodesOnly(omega, nodeOutEdges, decodedSv, 
                                                   decodedTvw, w, goalNode, seenNodes)

    strategy = {}
            
    decodedSv = decodeSv(nodes, model)
    #    print decodedSv

    decodedTvw = decodeTvw(edges, model)
    #    print decodedTvw

    # Check that the initial node is in the guessed nodes

    if (initialNode not in decodedSv):
        raise ValidationError("Initial node is not included in the model!")
    
    # Check that guessed reachable Eloise nodes have exactly one outgoing edge
    
    for v in eNodes:
        if (v not in decodedSv):
            break
        numOut = 0
        for w in nodeOutEdges[v]:
            if ([v,w] in decodedTvw):
                numOut += 1
                strategy[v] = w
        if (numOut != 1):
                raise ValidationError("Guessed reachable Eloise node %d does not have exactly one outgoing edge!" % (v))

    # Check that guessed reachable Abelard nodes have all outgoing edges

    for v in aNodes:
        if (v not in decodedSv):
            break
        numOut = 0
        for w in nodeOutEdges[v]:
            if ([v,w] in decodedTvw):
                numOut += 1
        if (numOut != len(nodeOutEdges[v])):
                raise ValidationError("Guessed reachable Abelard node %d does not have all of its %d outgoing edges!" % (v,len(nodeOutEdges[v])))

    # Check that all guessed edges force their destination state to the model
    
    for e in edges:
        (v,w) = e
        if ([v,w] in decodedTvw):
            if (w not in decodedSv):
                raise ValidationError("Node %d is not guessed reachable even though it has an incoming edge T_%d_%d) is" % (w, v, w))

    # Check that non-guessed nodes have no incoming edges

    for v in nodes:
        if (v in decodedSv):
            break
        numIn = 0
        for w in nodeInEdges[v]:
            if ([w,v] in decodedTvw):
                numIn += 1
        if (numIn != 0):
                raise ValidationError("Non-guessed node %d has incoming edges!" % (v))
            
    # Check that non-guessed nodes have no outgoing edges

    for v in nodes:
        if (v in decodedSv):
            break
        numOut = 0
        for w in nodeOutEdges[v]:
            if ([v,w] in decodedTvw):
                numOut += 1
        if (numOut != 0):
                raise ValidationError("Non-guessed node %d has outgoing edges!" % (v))

    # Check for if the model contains any loops Abelard would win by using a slow recursive approach

    for v in nodes:
        if (omega[v] != 1):
            break
        if (v not in decodedSv):
            break

        seenNodes = []
        goalReachableUsingPriorityOneNodesOnly(omega, nodeOutEdges, decodedSv, decodedTvw, v, v, seenNodes)      

    return strategy
        
# Extract the set of nodes given a list of edges

def extractNodes(edges):
    nodes = []
    for e in edges:
      (n1,n2) = e
      if n1 not in nodes: nodes.append(n1)
      if n2 not in nodes: nodes.append(n2)
    return nodes

# Solve a two-player parity game with two priorities 0 and 1
# - edges is the directed edge relation given as a list of (src,dst) pairs
# - initialNode is the initial node of the play
# - eNodes are nodes of the play controlled by Eloise, all other
#          nodes are controlled by Abelard
# - omega is a function from nodes to priorities 0 and 1
#         given as a dictionary
#
# See slides for description of parity games, some comments:
#
# - Eloise will win all plays where the priority 0 is seen
#   infinitely often
# - If Eloise has a winning strategy, she also has a positional
#   one, playing exactly the same outgoing edge each time she
#   leaves a node controlled by her
# - The main idea of the encoding is to guess Eloise's strategy,
#   compute a fixpoint of states and edges reachable by any play,
#   and then to add constraints which remove all models that contain
#   a loop where Abelard would win

def solveParity(edges, initialNode, eNodes, omega, out = sys.stdout):

    nofEdges = len(edges)
    assert(nofEdges >= 1)

    nodes = extractNodes(edges)
    nofNodes = len(nodes)

    assert initialNode in nodes
    assert(len(omega) == nofNodes)
    assert(len(eNodes) <= nofNodes)

    for n in nodes:
        found = False
        for e in edges:
            (n1,n2) = e
            if (n1 == n):
                found = True
                break
        if(found == False):
            assert(False)

    for en in eNodes:
        assert(en in nodes)

    aNodes = []
    for n in nodes:
        if n not in eNodes:
            aNodes.append(n)

    nodes.sort()
    eNodes.sort()
    aNodes.sort()
            
    omegaKeys = list(omega.keys())
    omegaKeys.sort()

    for n in omegaKeys:
        assert(n in nodes)
        o = omega[n]
        assert ((o == 0) or (o == 1))

    nodeOutEdges = {}
    for e in edges:
        (v, w) = e
        if v not in nodeOutEdges:
            nodeOutEdges[v] = [w]
        else:
            nodeOutEdges[v].append(w)

    nodeInEdges = {}
    for e in edges:
        (v, w) = e
        if w not in nodeInEdges:
            nodeInEdges[w] = [v]
        else:
            nodeInEdges[w].append(v)

    # Helper functions
    def p(txt):
        if out: out.write(txt+'\n')
    def pr(txt):
        if out: out.write(txt)

    solution = None
    p("---")
    p("%d nodes: %s" % (nofNodes,nodes))
    p("%d edges: %s" % (nofEdges,edges))
    p("initial node: %s" % initialNode)
    p("Eloise nodes: %s" % eNodes)
    p("Abelard nodes: %s" % aNodes)
    p("priorities: %s" % (omega))

    # Create one solver instance that we'll use all the time
    s = Solver()

    s.add(forceInitialNode(initialNode))

    if (len(eNodes) > 0):
        s.add(guessEloiseStrategy(eNodes, nodeOutEdges))

    if (len(aNodes) > 0):
        s.add(forceAbelardSuccessors(aNodes, nodeOutEdges))

    s.add(forceNodesWithIncomingEdges(nodes, nodeInEdges))

    s.add(removeAbelardWins(omega, edges))
    
    #    print s

    result = s.check()
    p("The solver says: "+str(result))

    strategy = {}
    
    if result == unsat:
        p("Abelard wins!")
        solution = "nonexistent"

    elif result == sat:
        model = s.model()

        #        print model
        
        strategy = checkSolution(edges, initialNode, nodes, eNodes, aNodes, 
                                 omega, nodeOutEdges, nodeInEdges, model, out)

        p("Eloise wins!")
        solution = "found"

    else:
        assert(result == unknown)
        p('"unknown" (with reason "'+ \
          s.reason_unknown()+ \
          '") returned by the solver, aborting!')
        solution = "error"

    if (len(strategy) != 0):
        p("Winning strategy for Eloise is: %s" % (str(strategy)))
        
    return (solution,strategy)

