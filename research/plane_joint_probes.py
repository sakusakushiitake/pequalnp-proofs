"""Find fixed AND-test sets for simultaneous same-side pairs in PG(2,3)."""

from collections import deque
from itertools import combinations

from plane_nonedge_orbits import EDGES, N, generators, move


def compose(first, second):
    return tuple(second[v] for v in first)


def inverse(perm):
    return tuple(perm.index(v) for v in range(len(perm)))


def group(gens):
    identity = tuple(range(2 * N))
    found = {identity}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for generator in gens:
            candidate = compose(current, generator)
            if candidate not in found:
                found.add(candidate)
                queue.append(candidate)
    return sorted(found)


def pair_words(seeds, actions):
    """Assign a word taking every reachable pair to its seed."""
    back = [inverse(g) for g in actions]
    seen = {p: (p, ()) for p in seeds}
    queue = deque(seeds)
    while queue:
        p = queue.popleft()
        root, word = seen[p]
        for k, g in enumerate(back):
            q = move(g, p)
            if q not in seen:
                seen[q] = root, (k,) + word
                queue.append(q)
    return seen


def balanced_tests(left, right, actions, collineations, first, orbit_of):
    """Classify pairs of test sets up to a collineation of the first set."""
    labels = {}
    for p, (_, word) in first.items():
        for q in combinations(right, 2):
            image = q
            for k in word:
                image = move(actions[k], image)
            labels[p, q] = 1 << orbit_of[image]
    full = (1 << len(set(orbit_of.values()))) - 1
    swap = generators()[2]
    def dual_labels(p,q):
        return labels[p,q] | labels[move(swap,q),move(swap,p)]
    results = {}
    for a,b in [(2,2),(2,3),(2,4),(2,5),(2,6),(3,3),(3,4),(4,4),(3,5)]:
        unseen = set(combinations(left,a))
        direct, dual = None, None
        while unseen and direct is None:
            s = min(unseen)
            unseen -= {move(g,s) for g in collineations}
            for t in combinations(right,b):
                hit, both = 0, 0
                for p in combinations(s,2):
                    for q in combinations(t,2):
                        hit |= labels[p,q]
                        both |= dual_labels(p,q)
                if both==full and dual is None:
                    dual=(s,t)
                if hit==full:
                    direct=(s,t)
                    break
        results[a,b]=(direct,dual)
    return results


def search():
    left = tuple(range(N))
    right = tuple(range(N, 2 * N))
    anchor = (0, 1)
    actions = [tuple(p) for p in generators()[:2]]
    collineations = group(actions)
    assert all({move(g, e) for e in EDGES} == EDGES for g in actions)
    first = pair_words([anchor], actions)
    assert set(first) == set(combinations(left, 2))
    stabilizer = [g for g in collineations if move(g, anchor) == anchor]
    residual = set(combinations(right, 2))
    orbit_of = {}
    sizes = []
    while residual:
        seed = min(residual)
        orbit = {move(g, seed) for g in stabilizer}
        assert orbit <= residual
        orbit_of.update((p, len(sizes)) for p in orbit)
        sizes.append(len(orbit))
        residual -= orbit
    for count in range(2, N + 1):
        solutions = [s for s in combinations(right, count)
                     if len({orbit_of[p] for p in combinations(s, 2)}) == len(sizes)]
        if solutions:
            break
    probes = min(solutions)
    # Index the whole stabilizer; a one-step certificate maps each remaining pair.
    second = {}
    for p in combinations(right, 2):
        index = next(i for i, g in enumerate(stabilizer) if set(move(g, p)) <= set(probes))
        second[p] = index
    for pair, (_, word) in first.items():
        for other in combinations(right, 2):
            p, q = pair, other
            for k in word:
                p, q = move(actions[k], p), move(actions[k], q)
            last = stabilizer[second[q]]
            assert move(last, p) == anchor and set(move(last, q)) <= set(probes)
    print("collineations", len(collineations), "stabilizer", len(stabilizer))
    print("stabilizer orbit sizes", sizes)
    print("least second-side test with the first pair fixed", probes, "solutions", len(solutions))
    print("certified combinations", len(first) * len(second))
    print("balanced tests", balanced_tests(left,right,actions,collineations,first,orbit_of))
    return actions, first, stabilizer, probes, second


if __name__ == "__main__":
    search()
