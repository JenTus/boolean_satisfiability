from z3 import *
import sys
# STUDENTS: do not add or modify import statements!

# The parts that you should fill in are marked with "INSERT YOUR CODE HERE"

# Persons are indentified by positive integers

# For a person p, the Boolean variable yea_p is true iff p votes "yea".

def vote(person):
    return Bool("yea_%d" % (person))

# The Boolean variable cnt_g_n_l means that at least n persons out of
# out of the first l persons in the group g vote "yea".

def count(g, n, l):
    return Bool("cnt_%d_%d_%d" % (g, n, l))

# Define the Boolean variable cnt_g_n_l recursively
# Note that persons[] should be indexed by l-1 rather than l

def countFormula(g, n, l, persons):
    if n == 1:
        if l == 1:
            return count(g, n, l) == vote(persons[0])
#            return count(g, n, l)
        else:
            return count(g, n, l) == Or(count(g, n, l-1), vote(persons[l-1]))
#            return count(g, n, l) # INSERT YOUR CODE HERE
    else:
        if l == n:
            return count(g, n, l) == And(count(g, n-1, l-1), vote(persons[l-1]))
#            return  count(g, n, l)# INSERT YOUR CODE HERE
        else:
            return count(g, n, l) == Or(And(count(g, n-1, l-1), vote(persons[l-1])), count(g, n, l-1))
#            return  count(g, n, l)# INSERT YOUR CODE HERE

# Count votes up to the given limit in a recursive fashion

def countVotesFormula(group, limit, persons):
    definitions = []
    for n in range(1,limit+1):                    # Count up to given limit
        for l in range(n,n+len(persons)-limit+1): # Indexing persons
            definitions.append(countFormula(group, n, l, persons))
    if definitions == []:
        return False
    else:
        return And(definitions)

# Ensure the clear majority of "yea" votes for the given group of persons

def testMajority(group, persons):
    n = len(persons)
    k = n//2+1 
   
    return And(countVotesFormula(group, k, persons), count(group, k, n)) 

# Ensure the clear minority of "yea" votes for the given group of persons

def testMinority(group, persons):
    n = len(persons)
    k = (n-1)//2 + 1 # INSERT YOUR CODE HERE
    return And(countVotesFormula(group, k, persons), Not(count(group,k,n))) # INSERT YOUR CODE HERE

# The rest of the program

class ValidationError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def checkSolution(majorities, minorities, persons, model, out = sys.stdout):
    """
    Print (and validate) the solution found 
    """
    # Helper functions
    def p(txt):
        if(out): out.write(txt+"\n")

    def countvotes(group, votes):
        cnt = 0
        for m in group:
            if m in votes:
                cnt +=1
        return cnt

    def majority(group, votes):
        if countvotes(group, votes) >= len(group)//2+1:
            return True

    def minority(group, votes):
        if countvotes(group, votes) < (len(group)-1)//2+1:
            return True

    # Extract votes from the model
    votes = []
    for p in persons:
        var = vote(p)
        val = model[var]
        if val == None:
            raise ValidationError("The value of yea_%d is not defined!" % (p))
        elif is_true(val):
            votes.append(p)

    # Check majority groups
    for maj in majorities:
        if not majority(maj, votes):
            raise ValidationError("Group %s has no majority!" % (maj))

    # Check minority groups
    for min1 in minorities:
        if not minority(min1, votes):
            raise ValidationError("Group %s is not in minority!" % (min1))

    return votes
        
def findVotes(majorities, minorities, out = sys.stdout):

    nofMaj = len(majorities)
    nofMin = len(minorities)
    groups = majorities+minorities
    nofg = len(groups)
    persons = []
    for g in groups:
      for p in g:
          if p not in persons:
              persons.append(p)
    nofp = len(persons)
    assert(nofg > 0)
    assert(nofp > 1)

    # Helper functions
    def p(txt):
        if out: out.write(txt+'\n')
    def pr(txt):
        if out: out.write(txt)

    solution = None
    p("---")
    p("%d persons divided in %d groups (%d majority, %d minority):" \
      % (nofp, nofg, nofMaj, nofMin))
    pr("majorities: ")
    for maj in majorities:
        pr("%s " % (maj))
    pr("\nminorities: ")
    for min in minorities:
        pr("%s " % (min))
    pr("\n")

    # Create one solver instance that we'll use all the time
    s = Solver()
    g = 1

    for maj in majorities:
        s.add(testMajority(g, maj))
        g += 1

    for min1 in minorities:
        s.add(testMinority(g, min1))
        g += 1

    votes = []
    result = s.check()
    p("The solver says: "+str(result))

    if result == unsat:
        p("No assignment of votes possible!")
        solution = "nonexistent"

    elif result == sat:
        model = s.model()
        votes = checkSolution(majorities, minorities, persons, model)
        p("Votes in the assignment: %s" % votes)
        solution = "found"

    else:
        assert(result == unknown)
        p('"unknown" (with reason "'+ \
          s.reason_unknown()+ \
          '") returned by the solver, aborting!')
        solution = "error"

    return (solution, votes)

