"""Compute the three symmetry classes of dirty-AND probes for L-meta-650.

The first thirteen vertices are lines, and the last thirteen are points.
Each returned word sends an unordered pair to the printed representative.
The graph edges, each permutation, and every word are checked directly.

For an existential circuit search it suffices to require that some AND
fires on the single independent input {0,1,17}, whenever the search is
restricted to circuits with some AND firing on some independent input.
The pair-tests theorem supplies a triggering singleton or nonedge pair.
Rename the input wires by the certified automorphism and apply monotonicity
from its image to this triple. Renaming preserves all gates, the output
function up to this automorphism, and the number of gates. The reverse
implication follows from independence of the triple. This reduction
quantifies over circuits; it does not classify an individual circuit by
running that circuit on just the triple.
"""
from collections import Counter, deque
from itertools import combinations_with_replacement

N = 13
DIFFERENCES = {0, 1, 3, 9}
EDGES = {
    (0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21),
    (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19),
    (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17),
    (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23),
    (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19),
    (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17),
    (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
    (12, 14), (12, 15), (12, 17), (12, 23)
}
REPS = ((0, 0), (0, 1), (0, 17))
FIXED_INPUT = frozenset({0, 1, 17})


def generators():
    point = [8, 6, 0, 1, 11, 9, 7, 4, 2, 5, 10, 3, 12]
    line = [5, 10, 0, 11, 8, 6, 4, 1, 2, 9, 7, 3, 12]
    rotations = [(i - 1) % N for i in range(N)] + [N + (i + 1) % N for i in range(N)]
    collineation = [(-line[-i % N]) % N for i in range(N)] + [N + i for i in point]
    duality = list(range(N, 2 * N)) + list(range(N))
    return [rotations, collineation, duality]


def move(permutation, pair):
    return tuple(sorted(permutation[i] for i in pair))


def certificates():
    assert EDGES == {(i, N + j) for i in range(N) for j in range(N) if (i + j) % N in DIFFERENCES}
    vertices = list(range(2 * N))
    actions = generators()
    for action in actions:
        assert sorted(action) == vertices
        assert {move(action, e) for e in EDGES} == EDGES
    inverse = [[p.index(i) for i in vertices] for p in actions]
    seen = {p: (p, ()) for p in REPS}
    queue = deque(REPS)
    while queue:
        current = queue.popleft()
        rep, word = seen[current]
        for k, perm in enumerate(inverse):
            previous = move(perm, current)
            if previous not in seen:
                seen[previous] = (rep, (k,) + word)
                queue.append(previous)
    assert set(seen) == set(combinations_with_replacement(vertices, 2)) - EDGES
    assert not any(set(edge) <= FIXED_INPUT for edge in EDGES)
    assert all(set(pair) <= FIXED_INPUT for pair in REPS)
    for pair, (representative, word) in seen.items():
        for k in word:
            pair = move(actions[k], pair)
        assert pair == representative
    # All generators preserve equality and same-side incidence type.
    for rep in REPS:
        for pair, (target, _) in seen.items():
            if target == rep:
                assert (pair[0] == pair[1]) == (rep[0] == rep[1])
                assert (pair[0] // N == pair[1] // N) == (rep[0] // N == rep[1] // N)
    return seen


if __name__ == '__main__':
    seen = certificates()
    print('representative multiplicities', dict(Counter(r for r, _ in seen.values())))
    print('maximum descent length', max(len(w) for _, w in seen.values()))
    print('one independent input containing every representative', sorted(FIXED_INPUT))
