# Local obstruction at 3 for the symmetric permanent level

Let J be the 4 by 4 all-ones matrix. A three-dimensional linear space of symmetric matrices satisfying per(J+X)=24 cannot be defined over the 3-adic rationals or any totally ramified quadratic or cubic extension of them. More generally, over a finite extension of Q₃ with ramification index at most three, its reduction cannot be any of the 32 planes defined over F₃. The 32 points themselves exist in characteristic three. The proof below allows arbitrary residue-field extensions throughout the obstruction computations, conditional on the reduced plane being defined over F₃.

Run `python verify.py --msolve /path/to/msolve` with Python 3, NumPy, SymPy and msolve. The F₃ Gröbner basis runs use its deterministic sparse linear algebra option. The arithmetic generation and ideal checks can also run separately with `--generate DIR` and `--check DIR`. Use a fresh directory for generated intermediates.

## The finite special fiber

Write r_k for the sum of all k-by-k subpermanents, with r₀=1. The coefficient of tᵏ in per(J+tX) equals (4−k)! r_k(X). Over characteristic zero, all four r_k vanish individually. Reduce these integral identities, retaining r₁ even at 3. Eliminate the final diagonal with r₁=0. The resulting projective space has nine homogeneous coordinates.

The enumeration finds 388 rational points, 488 rational lines, and 32 rational planes on this scheme. For a projective F₃ line, its four point evaluations detect homogeneous forms through degree three. A quartic vanishing at all four points is a multiple of s³t−st³. Its t-linear coefficient at (1,0) detects the remaining scalar. This gives a test for polynomial vanishing on each joining line. Every plane is obtained by extending a contained line by another point. For each reported plane the program also checks the 31 full coefficient equations of the plane independently. Vertex permutations divide the planes into four orbits of sizes 4,12,4,12.

## Integral local equations

Normalize three independent coordinate columns to the identity, allowing all 18 other coefficients to vary. Let B be the integer lift of the normalized F₃ basis, and F the vector of 31 integral equations. Let A be the Jacobian modulo 3, K a basis of its kernel, P a basis of its left kernel, and b=F(B)/3 modulo 3. Write Q and C for the degree-two and degree-three Taylor terms at B. They are obtained by polynomial arithmetic over the integers before reduction. This includes pure cubes in characteristic three.

A local-field plane has a full-rank reduction. One can first normalize at a minor of least valuation and then use any minor that remains nonzero at the residue point. This gives a point of the affine chart just described. For a uniformizer π with v(3)=e, expand its coordinates as B+πD+π²E+π³G+⋯. Digits can be lifted from the maximal unramified subfield. An unramified extension allows the leading unit of 3/πᵉ to be normalized to 1 by scaling π. Each projection by P eliminates the new digit multiplying A. A fixed invertible submatrix of A gives a particular solution whenever the projected equations vanish, and adding K times new parameters describes all solutions.

* At e=1 the equation A D=−b is inconsistent at all 32 points. The kernel dimensions are 4 at twelve points, 6 at sixteen, and 9 at four.
* At e=2, D belongs to ker A. The equations P(Q(D)+b)=0 have no solution over the algebraic closure at any of the 32 points.
* At e=3, first impose P Q(D)=0 and solve for E. At the next order impose P(C(D)+Q(D+E)−Q(D)−Q(E)+b)=0. Three orbits are already excluded. On the fourth orbit the first kernel parameters necessarily satisfy s₀=s₁=s₂=s₄=0 and s₃+s₅=1. Each necessity is checked by adjoining an inverse of the proposed vanishing expression and obtaining the unit ideal.

For that last orbit, write 3/π³=1+u₁π+u₂π²+⋯. The fourth-order equations force u₁=t₂=t₄=0 for the second kernel parameters t. The code also verifies that the free part of G has zero projected contribution at this order. After these substitutions the fifth-order equations contain both t₀ and t₀²+1, which are incompatible over every extension of F₃.

The fifth-order computation uses integral polynomials. If the formal coefficient of λʲ after substituting the chosen digits is cⱼ, then for π³=3 the digit at k is obtained from ∑ 3ⁱ c_{r+3i} divided by 3^{⌊k/3⌋}, where r=k mod 3 and 0≤i≤⌊k/3⌋. All lower residues vanish identically after the recorded substitutions, and every division is checked coefficientwise. For a general unit with u₁=0, the additional fifth-order term is u₂ b, retained as a free parameter. These are necessary equations for a characteristic-zero lift. The computation leaves residue points defined only over larger finite fields and ramification indices above three open.
