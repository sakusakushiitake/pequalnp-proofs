import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PermanentIsolated

-- The 24-term expansion follows the accepted project lemma L-gct-222.
lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def shift (X : Matrix (Fin 4) (Fin 4) ℂ) (t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => 1+t*X i j

set_option maxHeartbeats 8000000 in
theorem isolated_zero (X : Matrix (Fin 4) (Fin 4) ℂ)
    (level : ∀ t : ℂ, (shift X t).permanent = 24)
    (row : ∀ j : Fin 4, j ≠ 0 → X 0 j = 0) (col : ∀ j : Fin 4, j ≠ 0 → X j 0 = 0) :
    X 0 0 = 0 := by
  have test (t : ℂ) := level t
  simp only [perm4,shift,Matrix.of_apply,row 1 (by decide),row 2 (by decide),row 3 (by decide),
    col 1 (by decide),col 2 (by decide),col 3 (by decide),mul_zero,add_zero] at test
  let a := X 0 0
  have vanish : a^4 = 0 := by
    dsimp only [a]
    linear_combination
      ((2*(X 0 0)^3-6*(X 0 0)^2-3*X 0 0+3)/18)*(test 1) -
      ((2*(X 0 0)^3+6*(X 0 0)^2-3*X 0 0-3)/18)*(test (-1)) -
      ((2*(X 0 0)^3-3*(X 0 0)^2-12*X 0 0+6)/144)*(test 2) +
      ((2*(X 0 0)^3+3*(X 0 0)^2-12*X 0 0-6)/144)*(test (-2))
  by_contra no
  exact (pow_ne_zero _ no) vanish

/-- On every line in the permanent level, an isolated index has diagonal zero. -/
theorem isolated (X : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4)
    (level : ∀ t : ℂ, (shift X t).permanent = 24)
    (row : ∀ j, j ≠ i → X i j = 0) (col : ∀ j, j ≠ i → X j i = 0) : X i i = 0 := by
  let σ := Equiv.swap (0 : Fin 4) i
  have h0 : σ 0=i := Equiv.swap_apply_left ..
  have ne (j : Fin 4) (h : j≠0) : σ j ≠ i := fun e => h (σ.injective (e.trans h0.symm))
  have lev (t : ℂ) : (shift (X.submatrix σ σ) t).permanent = 24 := by
    change (((shift X t).submatrix σ id).submatrix id σ).permanent = 24
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols,level]
  have h := isolated_zero (X.submatrix σ σ) lev
    (fun j hj => by change X (σ 0) (σ j) = 0; rw [h0]; exact row _ (ne j hj))
    (fun j hj => by change X (σ j) (σ 0) = 0; rw [h0]; exact col _ (ne j hj))
  change X (σ 0) (σ 0) = 0 at h
  simpa [h0] using h

/-- Two directions in the same linear level space agree on the diagonal at i
whenever they agree on the off-diagonal row and column at i. -/
theorem diagonal_determined (L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ))
    (level : ∀ X ∈ L, (shift X 1).permanent = 24) (i : Fin 4)
    (A B : Matrix (Fin 4) (Fin 4) ℂ) (ha : A ∈ L) (hb : B ∈ L)
    (row : ∀ j, j ≠ i → A i j = B i j) (col : ∀ j, j ≠ i → A j i = B j i) : A i i = B i i := by
  have lev (t : ℂ) : (shift (A-B) t).permanent = 24 := by
    have h := level (t • (A-B)) (L.smul_mem t (L.sub_mem ha hb))
    simpa [shift,Matrix.smul_apply,smul_eq_mul] using h
  exact sub_eq_zero.mp (isolated (A-B) i lev
    (fun j hj => sub_eq_zero.mpr (row j hj)) (fun j hj => sub_eq_zero.mpr (col j hj)))

end PermanentIsolated
