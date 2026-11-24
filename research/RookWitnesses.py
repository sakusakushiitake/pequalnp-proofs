"""Exact lower bounds for complex level spaces of the 4-by-7 rook coefficients.

Run with Python 3. The cyclic construction uses the 28th cyclotomic field.
The sparse construction uses integer polynomial arithmetic.
"""
from itertools import combinations_with_replacement, permutations
from math import comb


def cyclic(degree):
    """The first degree coefficients vanish on a space of dimension 27 // degree."""
    n = 28
    modes = range(1, 1 + 27 // degree)
    # The simultaneous 4-cycle and 7-cycle labels each cell by its position in
    # the orbit. A matrix in mode k has entry zeta**(k * position).
    places = {(r, c): (21*r + 8*c) % n for r in range(4) for c in range(7)}
    assert set(places.values()) == set(range(n))
    assert all((places[((r+1) % 4, (c+1) % 7)] - v) % n == 1
               for (r, c), v in places.items())
    # Distinct characters have independently recoverable amplitudes. Pair a
    # column with the inverse character: its sum is 28 on the diagonal and
    # zero elsewhere by the finite geometric series.
    for a in modes:
        for b in modes:
            assert ((a-b) % n == 0) == (a == b)
    # Every rook coefficient is invariant under row and column permutations.
    # Its restriction to the modes has only weight-zero monomials. Check that
    # no such monomial of any relevant degree exists.
    for k in range(1, degree+1):
        weights = list(combinations_with_replacement(modes, k))
        assert len(weights) == comb(len(modes)+k-1, k)
        assert all(sum(w) % n != 0 for w in weights)
    return len(modes)


def sparse():
    """Independent check of all four restricted coefficients on an eight-plane."""
    # Linear entries are lists of (variable, signed integer coefficient).
    cells = {(0, j): [(j-1, 1)] for j in range(1, 7)}
    cells[0, 0] = [(a, -1) for a in range(6)]
    cells[1, 0] = [(6, 1)]
    cells[2, 0] = [(7, 1)]
    cells[3, 0] = [(6, -1), (7, -1)]
    pivots = [(0, j) for j in range(1, 7)] + [(1, 0), (2, 0)]
    assert [cells[p] for p in pivots] == [[(k, 1)] for k in range(8)]
    for degree in range(1, 5):
        coeff = {}
        # Count every matching exactly once by listing its rows in increasing order.
        from itertools import combinations, product
        for rows in combinations(range(4), degree):
            for cols in permutations(range(7), degree):
                for term in product(*(cells.get(p, []) for p in zip(rows, cols))):
                    monomial = tuple(sorted(a for a, _ in term))
                    sign = (-1) ** sum(b < 0 for _, b in term)
                    coeff[monomial] = coeff.get(monomial, 0) + sign
        assert not any(coeff.values()), (degree, coeff)
    return len(pivots)


if __name__ == "__main__":
    print("Cyclic dimensions for the first 1, 2, 3, 4 coefficients:",
          [cyclic(k) for k in range(1, 5)])
    print("Sparse dimension with all four coefficients zero:", sparse())
