from z3 import *
import sys
# STUDENTS: do not add or modify import statements!

#
# Some auxiliary functions are defined first, it is probably a good idea
# to have a look on them, too.
# The parts that you should fill are marked with "INSERT YOUR CODE HERE".
#

#
# Create new bucket variables for the time step i.
# Intuition: in a satisfying truth assignments, the value of bucket_b_at_i
# gives the amount of water contained in bucket b at time step i.
# Bucket numbering starts from 0, not 1.
#
def createBucketVars(i, nofBuckets):
    assert(isinstance(i, int) and i >= 1)
    return [Int("bucket_%d_at_%d" % (b,i)) for b in range(0, nofBuckets)]
    # The same without list comprehension would be as follows:
    #bucketAtI = []
    #for b in range(0, nofBuckets):
    #    bucketAtI.append(Int("bucket_%d_at_%d" % (b,i)))
    #return bucketAtI


#
# Create new boolean variables for selecting the actions.
# Intuitions:
# - If fill_b_at_i holds, then at i:th action the bucket b is filled,
#   i.e. the bucket b contains bucketCapacities[b] liters of water at
#   time step i+1
# - If empty_b_at_i holds, then at i:th action the bucket b is emptied,
#   i.e. the bucket b contains 0 liters of water at time step i+1
# - If pour_b1_to_b2_at_i holds, then at i:th action the contents of
#   the bucket b1 are poured into bucket b2,
#   i.e. at time step i+1 the bucket b2 contains the water it
#   contained at time step i and all the water of the bucket b1 that could fit
#   in b2; b1 contains the water it contained at time step i but
#   could not fit in b2.
#
def createActionSelectors(i, nofBuckets):
    assert(isinstance(i, int) and i >= 1)
    fillsAtI = [Bool("fill_%d_at_%d" % (b,i)) for b in range(0, nofBuckets)]
    emptiesAtI = [Bool("empty_%d_at_%d" % (b,i)) for b in range(0, nofBuckets)]
    poursAtI = [[(Bool("pour_%d_to_%d_at_%d" % (b1,b2,i)) if b1 != b2 else False) for b2 in range(0, nofBuckets)] for b1 in range(0, nofBuckets)]
    return (fillsAtI, emptiesAtI, poursAtI)


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


#
# Return a formula that evaluates to true if and only if
# exactly one of the action selector vars in actionSelectorsAtI does.
# This basically only takes care of the fact that poursAtI is
# a 2-dimensional array while fillsAtI and emptiesAtI are 1-dimensional.
#
def exactlyOneActionFormula(actionSelectorsAtI):
    (fillsAtI,emptiesAtI,poursAtI) = actionSelectorsAtI
    actionsAtI = fillsAtI + emptiesAtI
    for b1 in range(0, len(poursAtI)): actionsAtI += poursAtI[b1]
    return exactlyOneFormula(actionsAtI)


#
# Make and return the initial state constraint
# forcing that the buckets are empty in the beginning.
#
def initialStateFormula(bucketVarsAtI):
    assert(len(bucketVarsAtI) >= 1)
    return And([(bucketVar == 0) for bucketVar in bucketVarsAtI])

    
#
# Make and return the goal constraint stating that
# one of the buckets contains the correct (goal) liters of water.
#
def goalStateFormula(bucketVarsAtI, goal):
    assert(len(bucketVarsAtI) >= 1)
    assert(isinstance(goal, int) and goal >= 0)
    # INSERT YOUR CODE HERE and replace "True" with the real thing
    return exactlyOneFormula([(bucketVar == goal) for bucketVar in bucketVarsAtI])


#
# Make the formula enforcing that the step from the current state (bucketsAtI)
# to the next one (bucketsAtNextI) corresponds to the action selected
# (actionSelectorsAtI). Enforcing that exactly one action is taken is
# handled elsewhere, not to be worried here.
#
def stepFormula(bucketCapacities,
                bucketsAtI, actionSelectorsAtI, bucketsAtNextI):
    (fillsAtI, emptiesAtI, poursAtI) = actionSelectorsAtI
    nofBuckets = len(bucketCapacities)
    # The place to collect the implication constraint formulas
    constrs = []
    #
    # First, handle the fillsAtI actions
    #
    for b in range(0, nofBuckets):
        # Action: what happens to the bucket b
        act = bucketsAtNextI[b] == bucketCapacities[b]
        # Frame: The other buckets keep their value
        frame = True if nofBuckets <= 1 else And([(bucketsAtNextI[bf]==bucketsAtI[bf]) for bf in range(0, nofBuckets) if bf != b])
        constrs.append(Implies(fillsAtI[b], And(act, frame)))
    #
    # The same for emptiesAtI
    #
    # INSERT YOUR CODE HERE
    for b in range(0, nofBuckets):
        act = bucketsAtNextI[b] == 0
        frame = True if nofBuckets <= 1 else And([(bucketsAtNextI[bf]==bucketsAtI[bf]) for bf in range(0, nofBuckets) if bf != b])
        constrs.append(Implies(emptiesAtI[b], And(act, frame)))

    #
    # The same for poursAtI
    #
    # INSERT YOUR CODE HERE
    for b in range(0, nofBuckets):
        for b2 in range(0, nofBuckets):
            if b != b2:
                act1 = And(bucketsAtNextI[b2] == (bucketsAtI[b] + bucketsAtI[b2]), bucketsAtNextI[b] == 0,(bucketsAtI[b] + bucketsAtI[b2]) <= bucketCapacities[b2])
                act2 = And(bucketsAtNextI[b2] == bucketCapacities[b2], bucketsAtNextI[b] == bucketsAtI[b] - (bucketCapacities[b2] - bucketsAtI[b2]), (bucketsAtI[b] + bucketsAtI[b2]) > bucketCapacities[b2])
                act = Or(act1, act2)
                frame = True if nofBuckets <= 2 else And([(bucketsAtNextI[bf]==bucketsAtI[bf]) for bf in range(0, nofBuckets) if (bf != b and bf != b2)])
                constrs.append(Implies(poursAtI[b][b2], And(act, frame)))

    return And(constrs)
 

class TraceValidationError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def printSolution(bucketCapacities, goal, varDecls, bound, model, out = sys.stdout):
    """
    Print (and validate) the solution found 
    """
    assert(isinstance(bound, int) and bound >= 1)
    # 
    (bucketsAt,actionSelectorsAt) = varDecls
    nofBuckets = len(bucketsAt[0])

    # Some helper functions
    def p(txt):
        if(out): out.write(txt+"\n")

    def decodeState(i):
        state = []
        for b in range(0, nofBuckets):
            if model[bucketsAt[i-1][b]] == None:
                raise TraceValidationError("The model does not define the values of all the buckets")
            state.append(int(model[bucketsAt[i-1][b]].as_long()))
        return state
        
    prevState = None
    prevAction = None
    currentState = decodeState(1)
    for i in range(1, bound+1):
        p("  State "+str(i)+": "+str(currentState))

        for b in range(0, nofBuckets):
            if currentState[b] < 0 or currentState[b] > bucketCapacities[b]:
                raise TraceValidationError("The bucket %d contains illegal amount of water at time step %d" % (b, i))

        # Validate the previous action
        if i > 1:
            if prevAction[0] == 'fill':
                filledBucket = int(prevAction[1])
                if currentState[filledBucket] != bucketCapacities[filledBucket]:
                    raise TraceValidationError("The bucket %d is not properly filled at time step %d" % (filledBucket, i-1))
                for b in range(0, nofBuckets):
                    if b != filledBucket and prevState[b] != currentState[b]:
                        raise TraceValidationError("The amount of water in the bucket %d changes unexpectedly at time step %d" % (b, i-1))
            elif prevAction[0] == 'empty':
                emptiedBucket = int(prevAction[1])
                if currentState[emptiedBucket] != 0:
                    raise TraceValidationError("The bucket %d is not properly emptied at time step %d" % (emptiedBucket, i-1))
                for b in range(0, nofBuckets):
                    if b != emptiedBucket and prevState[b] != currentState[b]:
                        raise TraceValidationError("The amount of water in the bucket %d changes unexpectedly at time step %d" % (b, i-1))
            elif prevAction[0] == 'pour':
                fromBucket = int(prevAction[1])
                toBucket = int(prevAction[3])
                if not((prevState[fromBucket]+prevState[toBucket] ==
                        currentState[fromBucket]+currentState[toBucket]) and
                       (currentState[fromBucket] == 0 or
                        currentState[toBucket] == bucketCapacities[toBucket])):
                    raise TraceValidationError("The bucket %d is not properly poured into the bucket %d at time step %d" % (fromBucket, toBucket, i-1))
                for b in range(0, nofBuckets):
                    if b != fromBucket and b != toBucket and prevState[b] != currentState[b]:
                        raise TraceValidationError("The amount of water in the bucket %d changes unexpectedly at time step %d" % (b, i-1))
            else:
                raise TraceValidationError("The set of actions contains illegal variables")

        # Decode and validate the action
        if i < bound:
            prevState = currentState
            currentState = decodeState(i+1)
        
            (fillsAtI, emptiesAtI, poursAtI) = actionSelectorsAt[i-1]
            actionsAtI = fillsAtI + emptiesAtI
            for b1 in range(0, nofBuckets): actionsAtI += poursAtI[b1]
            trueActions = [act for act in actionsAtI if is_true(model[act])]
            if len(trueActions) == 0: raise TraceValidationError("No action selected at time step "+str(i))
            if len(trueActions) > 1: raise TraceValidationEror("More than one action selected at time step "+str(i))
            prevAction = str(trueActions[0]).split('_')
            p("  Action "+str(i)+": "+(' '.join(prevAction[:-2])))

    # Validate the goal
    goalBuckets = [b for b in range(0, nofBuckets) if currentState[b] == goal]
    if len(goalBuckets) == 0:
        raise TraceValidationError("None of the buckets in the last state contains %d liters of water" % goal)



def solveWithBMC(instance, maxBound, out = sys.stdout):
    assert(isinstance(maxBound, int) and maxBound >= 1)
    (bucketCapacities, goal) = instance
    assert(len(bucketCapacities) >= 1)
    assert(isinstance(goal, int))
    nofBuckets = len(bucketCapacities)

    def p(txt):
        if out: out.write(txt+'\n')

    solution = None

    for bound in range(1, maxBound+1):
        p("Getting the encoding for bound "+str(bound))

        # Bucket variables for all states
        bucketsAt = [createBucketVars(i, nofBuckets) for i in range(1, bound+1)]
        actionSelectorsAt = [createActionSelectors(i, nofBuckets) for i in range(1, bound)]

        # Create the solver instance
        s = Solver()

        # Force the initial state to be legal
        s.add(initialStateFormula(bucketsAt[1-1]))

        # Force the last state to be a goal state
        s.add(goalStateFormula(bucketsAt[bound-1], goal))

        # Must take exactly one action
        for i in range(1, bound):
            s.add(exactlyOneActionFormula(actionSelectorsAt[i-1]))

        # Encode the actions
        for i in range(1, bound):
            s.add(stepFormula(bucketCapacities,
                              bucketsAt[i-1], actionSelectorsAt[i-1], bucketsAt[i-1+1]))

        # Check if we have a solution already
        p("Solving the encoding for bound %d" % bound)
        result = s.check()
        p("Done, the result is: "+str(result))
        if result == unsat:
            # No solution yet
            # End of story?
            if bound == maxBound:
                solution = "not found"
                break
            continue
        elif result == sat:
            # Yes, a solution found!
            m = s.model()
            p("The bucket capacities are: "+str(bucketCapacities))
            p("The goal is: "+str(goal))
            p("The solution is:")
            printSolution(bucketCapacities, goal,
                          (bucketsAt,actionSelectorsAt), bound, m, out)
            solution = "found"
            break
        else:
            assert(result == unknown)
            p('"unknown" (with reason "'+s.reason_unknown()+'") returned by the solver, aborting')
            solution = "error"
            break;

    return solution
        


def solveWithIncrementalBMC(instance, maxBound, out = sys.stdout):
    assert(isinstance(maxBound, int) and maxBound >= 1)
    (bucketCapacities, goal) = instance
    assert(len(bucketCapacities) >= 1)
    assert(isinstance(goal, int))
    nofBuckets = len(bucketCapacities)

    def p(txt):
        if out: out.write(txt+'\n')

    solution = None

    # Bucket variables for the initial state (time 1)
    bucketsAtI = createBucketVars(1, nofBuckets)

    # We remember all the created state and action selection variables
    # because we need them when validating and printing the solution
    bucketsAt = []
    bucketsAt.append(bucketsAtI)
    actionSelectorsAt = []

    # Create one solver instance that we'll use all the time
    s = Solver()

    # Force the initial state to be legal
    p("Getting the encoding for bound 1")
    s.add(initialStateFormula(bucketsAtI))

    bound = 1
    while True:
        # Create a backtracking point for solver state
        s.push()
        # Temporarily force the last state to be a goal state
        s.add(goalStateFormula(bucketsAtI, goal))

        # Check if we have a solution already
        p("Solving the encoding for bound %d" % bound)
        result = s.check()
        p("Done, the result is: "+str(result))
        if result == unsat:
            # No solution yet
            # End of story?
            if bound == maxBound:
                solution = "not found"
                break
            # Retract the goal state formula
            s.pop()

            p("Getting the encoding for bound %d" % (bound+1))

            # Create action selector variables
            actionSelectorsAtI = createActionSelectors(bound, nofBuckets)
            actionSelectorsAt.append(actionSelectorsAtI)
            # Create next state bucket variables
            bucketsAtNextI = createBucketVars(bound+1, nofBuckets)
            bucketsAt.append(bucketsAtNextI)

            # Must take exactly one action
            s.add(exactlyOneActionFormula(actionSelectorsAtI))

            # Encode the actions
            s.add(stepFormula(bucketCapacities,
                              bucketsAtI, actionSelectorsAtI, bucketsAtNextI))

            bucketsAtI = bucketsAtNextI
            bound += 1
            continue
        elif result == sat:
            # Yes, a solution found!
            m = s.model()
            p("The bucket capacities are: "+str(bucketCapacities))
            p("The goal is: "+str(goal))
            p("The solution is:")
            printSolution(bucketCapacities, goal,
                          (bucketsAt,actionSelectorsAt), bound, m, out)
            solution = "found"
            break
        else:
            assert(result == unknown)
            p('"unknown" (with reason "'+s.reason_unknown()+'") returned by the solver, aborting')
            solution = "error"
            break;

    return solution
        
