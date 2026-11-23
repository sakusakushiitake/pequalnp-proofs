"""Check thirteen fixed independent inputs for screening every AND of L-meta-650.

The masks and checks need only the Python standard library. Bit i is the
input of vertex i in the statement. Each unordered nonedge pair (diagonal
included) is contained in a mask. The largest possible product |A|·|B| of
opposite sides of an independent set is twelve. The printed shapes provide
the input for the counting lower bound in the accompanying report.
"""
from collections import Counter
from itertools import combinations_with_replacement
from plane_nonedge_orbits import EDGES

MASKS = (393423, 2131485, 12820740, 19095696, 21292096, 25167747, 531063,
         1056059, 33561577, 43900960, 49965056, 58535936, 4276746)


def verify():
    full = (1 << 13) - 1
    neighbors = [sum(1 << (b-13) for a,b in EDGES if a == p) for p in range(13)]
    nonedge = set(combinations_with_replacement(range(26),2)) - EDGES
    covers = set()
    for mask in MASKS:
        assert mask >> 26 == 0
        side = [i for i in range(26) if mask >> i & 1]
        pairs = set(combinations_with_replacement(side,2))
        assert pairs.isdisjoint(EDGES)
        covers.update(pairs)
    assert covers == nonedge and len(covers) == 299 and len(set(MASKS)) == 13

    shapes = Counter()
    for a in range(1 << 13):
        b = full
        for p, row in enumerate(neighbors):
            if a >> p & 1:
                b &= ~row
        if all(a >> p & 1 or (b & row) for p,row in enumerate(neighbors)):
            shapes[a.bit_count(), b.bit_count()] += 1
    assert sum(shapes.values()) == 704
    assert max(a*b for a,b in shapes) == 12
    assert sorted({a*b for a,b in shapes}) == [0,9,12]
    # The nonincidence matrix has orthonormal rows over F2, hence rank 13.
    for p in range(13):
        for q in range(13):
            dot = ((full ^ neighbors[p]) & (full ^ neighbors[q])).bit_count()
            assert dot == (9 if p == q else 6)
    return sorted(shapes.items())


if __name__ == '__main__':
    print('13 independent inputs cover every one of the 299 nonedge pairs')
    print('maximal independent sets by shape', verify())
