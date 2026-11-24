import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace RookLevelSpace

open scoped BigOperators Matrix Kronecker
open Matrix Module

abbrev Idx (p q : ℕ) := Fin p × Fin q
abbrev V (p q : ℕ) := Idx p q → ℂ
def ones (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1
def off (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := ones n - 1
def A (p q : ℕ) : Matrix (Idx p q) (Idx p q) ℂ := off p ⊗ₖ off q
variable {p q : ℕ}
def U : Matrix (Idx p q) (Idx p q) ℂ := fun i j => if i.1 < j.1 ∧ i.2 ≠ j.2 then 1 else 0

lemma ones_square (n : ℕ) : ones n * ones n = (n : ℂ) • ones n := by
  ext i j
  simp [ones,Matrix.mul_apply]

lemma off_det {n : ℕ} (hn : 2 ≤ n) : (off n).det ≠ 0 := by
  let r : ℂ := (n : ℂ)-1
  have hr : r ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : n ≠ 1)
  have inv : off n * (ones n - r • 1) = r • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [off,sub_mul,mul_sub,mul_smul_comm,mul_one,one_mul,ones_square]
    unfold r
    simp only [smul_sub,sub_smul,one_smul]
    abel
  have eq := congrArg Matrix.det inv
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one] at eq
  intro h
  rw [h,zero_mul] at eq
  exact (pow_ne_zero _ hr) eq.symm

lemma nonsingular (hp : 2 ≤ p) (hq : 2 ≤ q) : (Matrix.toBilin' (A p q)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
  exact (Matrix.det_kronecker _ _).trans_ne (mul_ne_zero (pow_ne_zero _ (off_det hp)) (pow_ne_zero _ (off_det hq)))

lemma off_apply (i j : Fin p) : off p i j = if i=j then 0 else 1 := by
  by_cases eq : i=j <;> simp [off,ones,Matrix.one_apply,eq]

lemma a_apply (i j : Idx p q) : A p q i j = if i.1 ≠ j.1 ∧ i.2 ≠ j.2 then 1 else 0 := by
  change off p i.1 j.1 * off q i.2 j.2 = _
  by_cases r : i.1=j.1 <;> by_cases c : i.2=j.2 <;> simp [off_apply,r,c]
lemma split_matrix : A p q = U + U.transpose := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with lt | eq | gt
  · by_cases c : i.2 = j.2 <;>
      simp [a_apply,U,Matrix.transpose_apply,lt,lt.ne,not_lt.mpr lt.le,c,Ne.symm,eq_comm]
  · simp [a_apply,U,Matrix.transpose_apply,eq]
  · by_cases c : i.2 = j.2 <;>
      simp [a_apply,U,Matrix.transpose_apply,gt,gt.ne',not_lt.mpr gt.le,c,Ne.symm,eq_comm]

lemma transpose_eval (M : Matrix (Idx p q) (Idx p q) ℂ) (x y : V p q) :
    Matrix.toBilin' M.transpose x y = Matrix.toBilin' M y x := by
  rw [Matrix.toBilin'_apply,Matrix.toBilin'_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.transpose_apply,mul_comm,mul_left_comm]

lemma polar (x y : V p q) : Matrix.toBilin' (A p q) x y =
    Matrix.toBilin' U x y + Matrix.toBilin' U y x := by
  rw [split_matrix,map_add,LinearMap.add_apply,LinearMap.add_apply,transpose_eval]

def coeff (x : V p q) : ℂ := ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin p, ∑ b : Fin p,
  if a < b then x (a,j) * x (b,l) else 0

lemma coeff_as_form (x : V p q) : Matrix.toBilin' U x x = coeff x := by
  rw [Matrix.toBilin'_apply]
  simp only [Fintype.sum_prod_type,coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases jl : j=l
  · simp [U,jl]
  · simp only [if_neg jl]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ab : a<b <;> simp [U,jl,ab]


lemma off_row (i : Fin p) : ∑ j, off p i j = (p : ℂ) - 1 := by
  simp [off,ones,Matrix.one_apply,Finset.sum_sub_distrib]

lemma row_sum (i : Idx p q) : ∑ j, A p q i j = ((p:ℂ)-1)*((q:ℂ)-1) := by
  simp only [Fintype.sum_prod_type]
  change (∑ a : Fin p, ∑ b : Fin q, off p i.1 a * off q i.2 b) = _
  simp only [← Finset.mul_sum,off_row,← Finset.sum_mul]

lemma unit_eval (x : V p q) : Matrix.toBilin' (A p q) x (fun _ => 1) =
    (∑ i, x i) * (((p:ℂ)-1)*((q:ℂ)-1)) := by
  simp only [Matrix.toBilin'_apply,mul_one,← Finset.mul_sum,row_sum,Finset.sum_mul]

theorem quadratic_bound (hp : 2 ≤ p) (hq : 2 ≤ q) (L : Submodule ℂ (V p q))
    (linear : ∀ x ∈ L, (∑ i : Fin p, ∑ j : Fin q, x (i,j)) = 0)
    (quadratic : ∀ x ∈ L, coeff x = 0) : 2 * finrank ℂ L + 1 ≤ p*q := by
  let B := Matrix.toBilin' (A p q)
  have self (x) (hx : x ∈ L) : Matrix.toBilin' U x x = 0 := (coeff_as_form x).trans (quadratic x hx)
  have sub : L ≤ B.orthogonal L := by
    intro y hy x hx
    have t := self (x+y) (L.add_mem hx hy)
    simp only [map_add,LinearMap.add_apply,self x hx,self y hy,zero_add,add_zero] at t
    rw [show B x y = _ from polar x y]
    linear_combination t
  have bigger : L < B.orthogonal L := by
    apply lt_of_le_of_ne sub
    intro eq
    have h1 : (fun _ : Idx p q => (1:ℂ)) ∈ B.orthogonal L := by
      intro x hx
      rw [show B x _ = _ from unit_eval x,Fintype.sum_prod_type,linear x hx,zero_mul]
    rw [← eq] at h1
    have no := linear _ h1
    have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hq' : (q:ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    simpa [hp',hq'] using no
  have strict := Submodule.finrank_lt_finrank_of_lt bigger
  have orth := LinearMap.BilinForm.finrank_orthogonal (nonsingular hp hq) L
  change finrank ℂ (B.orthogonal L) = finrank ℂ (V p q) - finrank ℂ L at orth
  have dim : finrank ℂ (V p q) = p*q := by simp [V,Idx]
  rw [dim] at orth
  change finrank ℂ L < finrank ℂ (B.orthogonal L) at strict
  omega

end RookLevelSpace
