# Compiler Design - Summative
# First Order Logic Kompiler
#   - hsmm53

# Step 1
# Read input file

import sys
import re
from typing import List, Tuple, Set, Collection
from anytree import NodeMixin
from anytree.exporter import UniqueDotExporter

# The program expects one command line argument - the name of the file to be parsed
if len(sys.argv) != 2:
    print("Expected one argument - name of file")
    sys.exit(1)

# Read the input file
infile = sys.argv[1]
with open(infile) as f:
    tokens = f.read().split()

    categories = ["variables:", "constants:", "predicates:", "equality:",
                  "connectives:", "quantifiers:", "formula:"]

    data = {category[:-1]:[] for category in categories}

    # Make sure that the first token is the name of a valid set
    currentCategory = ""
    i = 0
    while not currentCategory:
        if tokens[i] in categories:
            currentCategory = tokens[i]

        i += 1

    # Now process the rest of the tokens
    for token in tokens[i:]:
        if token in categories:
            currentCategory = token
        else:
            data[currentCategory[:-1]].append(token)

    data['neg'] = [data['connectives'].pop(-1)]
    data['predicateNames'] = [p.split('[')[0] for p in data['predicates']]



    # The sets of variable names, constants etc. must be disjoint
    SymbolSet = Collection[str]
    def disjoint(sets: List[SymbolSet]) -> bool:
        checking_sets = [set(A) for A in sets]
        union = checking_sets[0]
        sym_diff = checking_sets[0]
        for T in checking_sets[1:]:
            union = union.union(T)
            sym_diff = sym_diff.symmetric_difference(T)

        if union == sym_diff:
            return True
        else:
            return False

    # This will fail if any symbol appears in multiple sets
    assert(disjoint([data['variables'], data['constants'], data['predicateNames'], data['equality'], data['connectives'], data['quantifiers'], data['neg']]))

    # Parentheses and comma are reservered characters
    for key, names in data.items():
        if not key == 'formula':
            for name in names:
                if '(' in name or ')' in name or ',' in name:
                    print(name)
                    print(key)
                    sys.exit(1)


    # We can now refine the tokens list and split any predicates into their individual characters
    pred = re.compile('^' + str(data['predicateNames']) + '\(.*\)')
    changes = []
    for i, token in enumerate(data['formula']):
        if pred.match(token):
            # Need to break it down further
            chars = [c for c in token]
            changes.append((i, chars))

    changes.reverse()
    for i, chars in changes:
        data['formula'] = data['formula'][:i] + chars + data['formula'][i+1:]

    eqs = []
    for i, token in enumerate(data['formula']):
        if token == data['equality'][0]:
            eqs.append(i)
    eqs.reverse()
    for i in eqs:
        if i + 1 == len(data['formula']):
            print("formula ends with the equality sign")
            sys.exit(1)

        # First check the variable/constant after the equality sign    
        right = data['formula'][i + 1]
        
        if right[-1] == ')':
            right = [right[:-1], ')']
        data['formula'] = data['formula'][:i+1] + right + data['formula'][i+2:]

        if i == 0:
            print("formula begins with the equality sign")
            sys.exit(1)

        # Then vaidate the variable/constant before it    
        left = data['formula'][i - 1]
        
        if left[0] == '(':
            left = ['(', left[1:]]
        data['formula'] = data['formula'][:i-1] + left + data['formula'][i:]


# We should now be ready to build a grammar
def pred(p:str) -> (List[str], str):
    parts = p.split('[')
    name = [parts[0], '(']
    full = parts[0] + '('
    
    count = int(parts[1][:-1]) # Remove the ']' at the end
    for i in range(count - 1):
        name.append(N['V'])
        name.append(',')
        full += N['V'] + ','

    name.append(N['V'])
    name.append(')')
    full += N['V'] + ')'
    return name, full

N = {'S':'START', 'Q':'QUAL', 'V':'VAR', 'P':'PRED', 'L':'VALUE', 'C':'CONNECT', 'B':'BRACKETED'}

Nreverse = {value:key for key, value in N.items()}
Nset = {x for x in N.values()}

T = ['(', ')', ',']
T += [x for x in data['variables']] + [x for x in data['constants']]
T += [x for x in data['equality']] + [x for x in data['quantifiers']]
T += [pred(x)[0][0] for x in data['predicates']] + [x for x in data['connectives']] + [data['neg'][0]]
T = set(T)

NandT = Nset.intersection(T)
while len(NandT) > 0:
    to_fix = NandT.pop()
    solved = to_fix
    while solved in T:
        # Make this symbol unique by adding a suffix
        solved += '(NT)'
    N[Nreverse[to_fix]] = solved


grammar = {N['S']:[['(', N['S'], ')'], [N['Q'], N['V'], N['S']], [N['P']], ['(', N['B'], ')'], [data['neg'][0], N['S']]],
           N['B']:[[N['L'], data['equality'][0], N['L']], [N['S'], N['C'], N['S']]],
           N['L']:[[x] for x in data['variables'] + data['constants']],
           N['V']:[[x] for x in data['variables']],
           N['Q']:[[x] for x in data['quantifiers']],
           N['P']:[pred(x)[0] for x in data['predicates']],
           N['C']:[[x] for x in data['connectives']]}

# To output the grammar in a nice format we define the display() function
def display(left: str, right: List[str]) -> str:
    s = left + " ->"
    for x in right[:-1]:
        for y in x:
            s += ' ' + y
        s += ' |'
    for y in right[-1]:
        s += ' ' + y
    return s

# Print sets of terminals and non-terminals
Nstr = "Non-terminal characters:\n{"
for c in N.values():
    Nstr += c + ' '
Nstr = Nstr[:-1] + '}\n'
print(Nstr)

Tstr = "Terminal characters:\n{"
for c in T:
    Tstr += c + ' '
Tstr = Tstr[:-1] + '}\n'
print(Tstr)

# Print the grammar rules
print("Grammar rules:")
for left, right in grammar.items():
    print(display(left, right))


# To help build a parse tree we define a node class
class ParseNode(NodeMixin):
    def __init__(self, name: str, parent=None, children=None):
        super(ParseNode, self).__init__()
        self.name = name
        print(f" the child is {children}")
        if children:
            print("thus")
            self.children = tuple(children)
        else:
            print("hence")
            self.children = tuple()
        self.parent = parent
        self.rule = [] # leaf nodes have no rule

    def define(self, rule):
        self.rule = rule

    def isComplete(self) -> bool:
        return len(self.children) == len(self.rule)

    def grow(self, child: str):
        # Extends parse tree according to this rule
        if self.children:
            _old_kids = list(self.children)
            _new_kids = _old_kids.append(ParseNode(child, parent=self))
            self.children = tuple(_new_kids)
        else:
            self.children = (ParseNode(child, parent=self))

    def tokens(self) -> List[str]:
        # Base case - terminal characters will always have an empty child list
        if self.children == []:
            return [self.symbol]

        ans = [c.tokens() for c in self.children]
        return ans


# Check if LL(1) Grammar
dict_first_empty = dict()
dict_first = dict()
def FIRST(a: List[str]) -> Set[str]:
    first_a = set()
    if len(a) == 0:
        first_a.add('')
        return first_a

    if len(a) == 1: # a single symbol
        a = a[0]
        if a in dict_first:
            return dict_first[a]
        
        if a in T:
            # Terminal symbols return a set containing only themselves
            first_a = {a}
            dict_first_empty[a] = False
            dict_first[a] = frozenset(first_a)
            return first_a
        elif a in N.values():
            if not a in grammar:
                # No production rules exist so this is a useless symbol
                # Return the empty set
                return first_a
            
            # if a -> empty string is a rule, add empty string to FIRST(a)
            if [''] in grammar[a]:
                first_a.add('')
                dict_first_empty[a] = True

            for rule in grammar[a]:
                if not rule == ['']:
                    adding = set()
                    for i, Y in enumerate(rule):
                        fY = FIRST([Y])
                        adding.update(fY)
                        if not '' in fY:
                            adding.discard('')
                            break
                    
                    first_a.update(adding)
                    
            # Once all production rules are processed we can determine the final set of the character
            if '' in first_a:
                dict_first_empty[a] = True
            else:
                dict_first_empty[a] = False
            dict_first[a] = first_a
            return first_a
        else:
            # oops
            return first_a
        
        
    else:
        adding = set()
        for i, X in enumerate(a):
            fX = FIRST([X])
            adding.update(fX)
            if not '' in fX:
                adding.discard('')
                break
        first_a.update(adding)
        return first_a

follow = {n:set() for n in N.values()}
follow[N['S']].add('\t')#end of file symbol is \t
subsets = set()
for left, right in grammar.items():
    for i, a in enumerate(right):
        if a in N.values():
            beta = right[i + 1:]
            fbeta = FIRST(beta)
            follow[left].update(fbeta)
            if '' in fbeta:
                follow[left].discard('')
                subsets.add((left, a))
    

for n in N.values():
    FIRST(n)
for t in T:
    FIRST(t)

# Given an LL(1) Grammar we can build a predictive parsing table M
M = {n:{t:None for t in T} for n in N.values()}
for left, right in grammar.items():
    for rule in right:
        for t in FIRST(rule):
            if t == '':
                for b in follow(left):
                    M[left][b] = rule
            else:
                M[left][t] = rule

# Now we build the parse tree
S = ['\t', N['S']]
f = iter(data['formula'])
try:
    c = next(f)
except StopIteration:
    print("Empty formula is not accepted")
    
i = 0
root = ParseNode(S[1])
working_node = root

while not S == ['\t']:
    print(S[::-1])
    # Pop out the top element of the stack since it is not yet the end of file symbol
    top = S.pop()
    if top in T: # Either top is a terminal...
        if top == c:
            # All is well so read in next symbol
            try:
                c = next(f)
            except StopIteration:
                if S == ['\t']:
                    break
                else:
                    print("Ran out of characters with stack as:\n\t")
                    print(S)
                    break
            # add leaf to tree
            working_node = ParseNode(top, parent=working_node)
            # and then move back up to nearest incomplete ancestor
            while working_node.isComplete():
                working_node = working_node.parent
        else:
            print(f"Expected to see {top} but formula contains {c} instead")
            break
    else: # Or a non-terminal.
        rule = M[top][c]
        if rule == None: # No rule is defined for this
            print(f"Error: a {top} cannot begin with {c}")
            break
        # If a valid rule is available add it to stack
        # We must reverse the list to do this

        # We add the new symbol to the tree
        # And since it is a non-terminal we recurse into it
        working_node = ParseNode(top, parent=working_node)
        working_node.rule = rule
        S.extend(rule[::-1])
    

print(S)
UniqueDotExporter(root).to_dotfile("parsetree.dot")

from graphviz import Source
#Source.from_file('parsetree.dot')

from graphviz import render
#render('dot', 'png', 'parsetree.png')
print("Done")
    

