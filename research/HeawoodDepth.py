"""Determine the minimum monotone binary formula depth for the graph of L-meta-1620.

Run with Python 3 and NumPy. Bits 0..20 in a truth signature correspond to the
21 graph edges. Bits 21..57 correspond to the 37 maximal independent sets.
The computation enumerates through depth three and then reasons about the two
possible gate types at depths four and five. No graph symmetry pruning is used.
"""
from itertools import combinations_with_replacement

import numpy as np


NEIGHBORS = ((7, 8, 10), (7, 9, 13), (8, 12, 13), (7, 11, 12),
             (10, 11, 13), (9, 10, 12), (8, 9, 11))
EDGES = sorted((1 << i) | (1 << j) for i, row in enumerate(NEIGHBORS) for j in row)


def target(x):
    return any(x & edge == edge for edge in EDGES)


def next_layer(values):
    # Repeated operands include all formulas from the preceding layer.
    return {out for a, b in combinations_with_replacement(values, 2)
            for out in (a & b, a | b)}


def minimal_masks(values):
    """Discard supersets. A disjoint pair exists iff two minimal masks are disjoint."""
    array = np.array(sorted(values), dtype=np.uint64)
    unseen = set(values)
    kept = []
    for value in sorted(values, key=lambda x: (x.bit_count(), x)):
        if value in unseen:
            kept.append(value)
            unseen.difference_update(array[(array & np.uint64(value)) == np.uint64(value)].tolist())
    return kept


def intersect_pairwise(masks):
    return all(a & b for a, b in combinations_with_replacement(masks, 2))


def evaluate():
    negatives = [x for x in range(1 << 14) if not target(x) and
                 all(target(x | (1 << i)) for i in range(14) if not (x >> i) & 1)]
    assert len(EDGES) == 21 and len(negatives) == 37
    tests = EDGES + negatives
    atoms = {sum(bool(x >> i & 1) << j for j, x in enumerate(tests)) for i in range(14)}
    one = next_layer(atoms)
    two = np.array(sorted(next_layer(one)), dtype=np.uint64)
    assert (len(atoms), len(one), len(two)) == (14, 196, 16019)
    positive_bits = np.uint64((1 << 21) - 1)
    low_19 = np.uint64((1 << 19) - 1)
    counts = np.array([i.bit_count() for i in range(1 << 21)], dtype=np.uint8)

    safe_max = complete_max = 0
    accepted_negatives = set()
    missed_edges = set()
    for i, x in enumerate(two):
        for signatures in (x & two[i:], x | two[i:]):
            p = signatures & positive_bits
            n = signatures >> np.uint64(21)
            yes = counts[p]
            no = 37 - counts[n & low_19] - counts[n >> np.uint64(19)]
            safe_max = max(safe_max, int(yes[n == 0].max(initial=0)))
            complete_max = max(complete_max, int(no[p == positive_bits].max(initial=0)))
            accepted_negatives.update(np.unique(n[yes >= 11]).tolist())
            missed_edges.update(np.unique(positive_bits ^ p[no >= 19]).tolist())

    pos_family = minimal_masks(accepted_negatives)
    neg_family = minimal_masks(missed_edges)
    assert (safe_max, complete_max) == (4, 1)
    assert len(pos_family) == 1162 and intersect_pairwise(pos_family)
    assert len(neg_family) == 10262 and intersect_pairwise(neg_family)

    # A depth-four OR rejecting every negative has two safe children, covering
    # at most 4+4 edges. A depth-four AND covering 11 edges has two children
    # covering at least 11 each. They accept a common negative by pos_family.
    # Dually a depth-four AND accepting all edges rejects at most 1+1 negatives.
    # A depth-four OR rejecting 19 negatives has children missing a common edge.
    # At depth five an OR covering all 21 edges needs a child covering >=11,
    # and an AND rejecting all 37 negatives needs a child rejecting >=19.
    # These cases exhaust the depth-five roots.
    # For the upper bound, each star uses depth three and the seven stars
    # are combined using a balanced OR tree of depth three.
    for x in range(1 << 14):
        by_stars = any(bool(x >> i & 1) and any(x >> j & 1 for j in row)
                       for i, row in enumerate(NEIGHBORS))
        assert by_stars == target(x)
    return {'depth': 6, 'depth_three_safe_edges': safe_max,
            'depth_three_complete_rejections': complete_max,
            'minimal_negative_masks': len(pos_family), 'minimal_edge_masks': len(neg_family)}


if __name__ == '__main__':
    print(evaluate())
