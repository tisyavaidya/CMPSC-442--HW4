############################################################
# CMPSC 442: Logic
############################################################

student_name = "Tisya Vaidya"

############################################################
# Imports
############################################################

# Include your imports here, if any are used.



############################################################
# Section 1: Propositional Logic
############################################################


class Expr(object):
    def __hash__(self):
        return hash((type(self).__name__, self.hashable))

class Atom(Expr):
    def __init__(self, name):
        self.name = name
        self.hashable = name

    def __hash__(self):
        return hash((type(self).__name__, self.name))

    def __eq__(self, other):
        return isinstance(other, Atom) and self.name == other.name

    def __repr__(self):
        return f"Atom({self.name})"

    def atom_names(self):
        return {self.name}

    def evaluate(self, assignment):
        return assignment[self.name]

    def to_cnf(self):
        return self


class Not(Expr):
    def __init__(self, arg):
        self.arg = arg
        self.hashable = arg

    def __hash__(self):
        return hash((type(self).__name__, self.arg))

    def __eq__(self, other):
        return isinstance(other, Not) and self.arg == other.arg

    def __repr__(self):
        return f"Not({self.arg})"

    def atom_names(self):
        return self.arg.atom_names()

    def evaluate(self, assignment):
        return not self.arg.evaluate(assignment)

    def to_cnf(self):
        if isinstance(self.arg, Atom):
            return self
        elif isinstance(self.arg, Implies):
            return And(self.arg.left.to_cnf(), Not(self.arg.right).to_cnf()).to_cnf()
        elif isinstance(self.arg, And):
            return Or(*[Not(conj).to_cnf() for conj in self.arg.conjuncts]).to_cnf()
        elif isinstance(self.arg, Not):
            return self.arg.arg.to_cnf().to_cnf()
        elif isinstance(self.arg, Iff):
            return Or(Not(Implies(self.arg.left, self.arg.right)).to_cnf(),
                      Not(Implies(self.arg.right, self.arg.left)).to_cnf()).to_cnf()
        elif isinstance(self.arg, Or):
            return And(*[Not(disj).to_cnf() for disj in self.arg.disjuncts]).to_cnf()


class And(Expr):
    def __init__(self, *conjuncts):
        self.conjuncts = frozenset(conjuncts)
        self.hashable = self.conjuncts

    def __hash__(self):
        return hash((type(self).__name__, self.conjuncts))

    def __eq__(self, other):
        return isinstance(other, And) and self.conjuncts == other.conjuncts

    def __repr__(self):
        return f"And({', '.join(map(repr, self.conjuncts))})"

    def atom_names(self):
        return {name for conjunct in self.conjuncts for name in conjunct.atom_names()}

    def evaluate(self, assignment):
        return all(conjunct.evaluate(assignment) for conjunct in self.conjuncts)

    def to_cnf(self):
        cnf_conjuncts = []
        for expr in self.conjuncts:
            cnf_expr = expr.to_cnf() if hasattr(expr, 'to_cnf') else expr  # Handle if it's already in CNF
            if isinstance(cnf_expr, And):
                cnf_conjuncts.extend(cnf_expr.conjuncts)
            else:
                cnf_conjuncts.append(cnf_expr)
        return And(*cnf_conjuncts)


class Or(Expr):
    def __init__(self, *disjuncts):
        self.disjuncts = frozenset(disjuncts)
        self.hashable = self.disjuncts

    def __hash__(self):
        return hash((type(self).__name__, self.disjuncts))

    def __eq__(self, other):
        return isinstance(other, Or) and self.disjuncts == other.disjuncts

    def __repr__(self):
        return f"Or({', '.join(map(repr, self.disjuncts))})"

    def atom_names(self):
        return {name for disjunct in self.disjuncts for name in disjunct.atom_names()}

    def evaluate(self, assignment):
        return any(disjunct.evaluate(assignment) for disjunct in self.disjuncts)

    def to_cnf(self):
        cnf_disjuncts = []
        for disjunct in self.disjuncts:
            if isinstance(disjunct, Or):  # Applying distribution
                cnf_disjuncts.extend(disjunct.to_cnf().disjuncts)
            elif isinstance(disjunct, And):  # De Morgan's laws
                cnf_disjuncts.append(And(*[Not(d).to_cnf() if isinstance(d, Not) else d.to_cnf() for d in disjunct.disjuncts]))
            elif isinstance(disjunct, Not):
                cnf_disjuncts.append(disjunct)
            else:
                cnf_disjuncts.append(disjunct.to_cnf())

        return Or(*cnf_disjuncts).to_cnf()


class Implies(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)

    def __hash__(self):
        return hash((type(self).__name__, self.left, self.right))

    def __eq__(self, other):
        return isinstance(other, Implies) and self.left == other.left and self.right == other.right

    def __repr__(self):
        return f"Implies({self.left}, {self.right})"

    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())

    def evaluate(self, assignment):
        return (not self.left.evaluate(assignment)) or self.right.evaluate(assignment)

    def to_cnf(self):
        return Or(Not(self.left).to_cnf(), self.right.to_cnf())


class Iff(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)

    def __hash__(self):
        return hash((type(self).__name__, self.left, self.right))

    def __eq__(self, other):
        return isinstance(other, Iff) and ((self.left == other.left and self.right == other.right) or
                                           (self.left == other.right and self.right == other.left))

    def __repr__(self):
        return f"Iff({self.left}, {self.right})"

    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())

    def evaluate(self, assignment):
        return self.left.evaluate(assignment) == self.right.evaluate(assignment)

    def to_cnf(self):
        return Or(And(self.left, self.right), And(Not(self.left), self.right), And(self.left, Not(self.right))).to_cnf()


def satisfying_assignments(expr):
    atoms = list(expr.atom_names())
    num_atoms = len(atoms)
    for i in range(2 ** num_atoms):
        assignment = {atoms[j]: (i >> (num_atoms - 1 - j)) & 1 == 1 for j in range(num_atoms)}
        if expr.evaluate(assignment):
            yield assignment


class KnowledgeBase(object):
    def __init__(self):
        self.facts = set()

    def get_facts(self):
        return self.facts

    def tell(self, expr):
        self.facts.add(expr.to_cnf())

    def ask(self, expr):
        negated_expr = Not(expr)
        assumption = And(*self.facts, negated_expr)
        assumption_cnf = assumption.to_cnf()
        for assignment in satisfying_assignments(assumption_cnf):
            return False 
        return True 


############################################################
# Section 2: Logic Puzzles
############################################################

# Puzzle 1

# Populate the knowledge base using statements of the form kb1.tell(...)
kb1 = KnowledgeBase()
kb1.tell(Implies(Atom("mythical"),Not(Atom("mortal"))))
kb1.tell(Implies(Not(Atom("mythical")),And(Atom("mortal"),Atom("mammal"))))
kb1.tell(Implies(Or(Not(Atom("mortal")),Atom("mammal")),Atom("horned")))
kb1.tell(Implies(Atom("horned"),Atom("magical")))

# Write an Expr for each query that should be asked of the knowledge base
mythical_query = Atom("mythical")
magical_query = Atom("magical")
horned_query = Atom("horned")

# Record your answers as True or False; if you wish to use the above queries,
# they should not be run when this file is loaded
is_mythical = False
is_magical =True
is_horned =True

# Puzzle 2

# Write an Expr of the form And(...) encoding the constraints
party_constraints = [
    Implies(Or(Atom("m"), Atom("a")), Atom("j")),
    Implies(Not(Atom("m")), Atom("a")),
    Implies(Atom("a"), Not(Atom("j")))
]

party_constraints = And(*party_constraints)

# Compute a list of the valid attendance scenarios using a call to
# satisfying_assignments(expr)
valid_scenarios = list(satisfying_assignments(party_constraints))

# Write your answer to the question in the assignment
puzzle_2_question = """
The guests can attend the party if either Mary and John come or only Ann comes.
"""

# Puzzle 3

# Populate the knowledge base using statements of the form kb3.tell(...)
kb3 = KnowledgeBase()
kb3.tell(Iff(Atom("p1"), And(Atom("p1"), Not(Atom("e2")))))
kb3.tell(Iff(Atom("p2"), Or(Atom("p2"), Atom("e2"))))
kb3.tell(Or(Atom("s1"), Atom("s2")))

# Write your answer to the question in the assignment; the queries you make
# should not be run when this file is loaded
puzzle_3_question = """
The correct state of affairs is that the first room contains a prize and the second room is empty.
"""

# Puzzle 4

# Populate the knowledge base using statements of the form kb4.tell(...)
kb4 = KnowledgeBase()
Adams = Atom("ia")
Brown = Atom("ib")
Clark = Atom("ic")
k_Adams = Atom("ka")
k_Brown = Atom("kb")
k_Clark = Atom("kc")

kb4.tell(k_Brown)
kb4.tell(Not(k_Clark))

# Uncomment the line corresponding to the guilty suspect
#guilty_suspect = "Adams"
guilty_suspect = "Brown"
# guilty_suspect = "Clark"

# Describe the queries you made to ascertain your findings
puzzle_4_question = """
To determine the guilty suspect, I queried whether it is not the case that all suspects are innocent.
"""
