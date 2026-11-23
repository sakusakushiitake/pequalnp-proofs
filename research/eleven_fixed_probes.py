"""Optimal fixed independent-input tests for L-meta-1342's 11-vertex graph.

The public search divides its dirty-AND case among 24 maximal independent
inputs. Exactly ten fixed independent inputs suffice to cover the nonedge
pairs. The lower bound uses integer weights totalling 19, with at most two
units in each independent set. All checks use only the standard library.
"""
from itertools import combinations_with_replacement

EDGES = {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}
TESTS = [(0,2,6,8),(1,3,9,10),(0,2,3,8),(0,4,5,7),(2,4,6,9),
         (0,1,5,6),(1,5,7,10),(7,8,10),(0,1,2,7),(0,3,4,5)]
WEIGHTS = {(1,2):1,(1,7):1,(3,4):1,(3,5):1,(3,8):2,(4,7):2,
           (4,9):1,(5,6):2,(5,10):1,(6,8):2,(6,9):1,(7,8):2,(9,10):2}


def verify():
    nonedges = set(combinations_with_replacement(range(11),2)) - EDGES
    assert len(nonedges) == 50 and set(WEIGHTS) <= nonedges
    covered = set()
    for test in TESTS:
        covered.update(combinations_with_replacement(sorted(test),2))
    assert covered == nonedges and len(TESTS) == 10
    assert sum(WEIGHTS.values()) == 19
    count = 0
    maximal = 0
    for mask in range(1 << 11):
        vertices = {i for i in range(11) if mask >> i & 1}
        if any({u,v} <= vertices for u,v in EDGES):
            continue
        count += 1
        if all(any({u,v} <= vertices | {i} for u,v in EDGES)
               for i in range(11) if i not in vertices):
            maximal += 1
        weight = sum(w for (p,q),w in WEIGHTS.items() if {p,q} <= vertices)
        assert weight <= 2
    assert maximal == 24
    return count,maximal


if __name__ == '__main__':
    print('independent and maximal independent inputs:', verify())
    print('minimum fixed test count: 10; integer-weight certificate: 19/2')
