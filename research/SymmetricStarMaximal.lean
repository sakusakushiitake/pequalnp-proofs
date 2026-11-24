import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace SymmetricStarMaximal

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

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
def mat (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j =>
  (![![h0*z + 1, h1*z + u + 1, h2*z + v + 1, h3*z - u - v + 1],
    ![h1*z + u + 1, h4*z + 1, h5*z + 1, h6*z + 1],
    ![h2*z + v + 1, h5*z + 1, h7*z + 1, h8*z + 1],
    ![h3*z - u - v + 1, h6*z + 1, h8*z + 1, h9*z + 1]] : Fin 4 → Fin 4 → ℂ) i j

def d1 (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) : ℂ :=
  6*h0 + 12*h1 + 12*h2 + 12*h3 + h4*u^2 - 4*h4*u + 6*h4 + 2*h5*u*v - 4*h5*u - 4*h5*v + 12*h5 - 2*h6*u^2 - 2*h6*u*v + 4*h6*v + 12*h6 + h7*v^2 - 4*h7*v + 6*h7 - 2*h8*u*v + 4*h8*u - 2*h8*v^2 + 12*h8 + h9*u^2 + 2*h9*u*v + 4*h9*u + h9*v^2 + 4*h9*v + 6*h9

def d2 (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) : ℂ :=
  2*h0*h4 + 4*h0*h5 + 4*h0*h6 + 2*h0*h7 + 4*h0*h8 + 2*h0*h9 + 2*h1^2 + 4*h1*h2 + 4*h1*h3 - 2*h1*h5*u + 4*h1*h5 - 2*h1*h6*u + 4*h1*h6 - 2*h1*h7*v + 4*h1*h7 + 2*h1*h8*u + 8*h1*h8 + 2*h1*h9*u + 2*h1*h9*v + 4*h1*h9 + 2*h2^2 + 4*h2*h3 - 2*h2*h4*u + 4*h2*h4 - 2*h2*h5*v + 4*h2*h5 + 2*h2*h6*v + 8*h2*h6 - 2*h2*h8*v + 4*h2*h8 + 2*h2*h9*u + 2*h2*h9*v + 4*h2*h9 + 2*h3^2 - 2*h3*h4*u + 4*h3*h4 - 2*h3*h5*u - 2*h3*h5*v + 8*h3*h5 + 2*h3*h6*u + 2*h3*h6*v + 4*h3*h6 - 2*h3*h7*v + 4*h3*h7 + 2*h3*h8*u + 2*h3*h8*v + 4*h3*h8 + h4*h7*u^2 + 2*h4*h7*u*v - 2*h4*h7*u + h4*h7*v^2 - 2*h4*h7*v + 2*h4*h7 - 2*h4*h8*u*v - 2*h4*h8*u - 2*h4*h8*v^2 + 4*h4*h8 + h4*h9*v^2 + 2*h4*h9*v + 2*h4*h9 + h5^2*u^2 + 2*h5^2*u*v - 2*h5^2*u + h5^2*v^2 - 2*h5^2*v + 2*h5^2 - 2*h5*h6*u*v - 2*h5*h6*u - 2*h5*h6*v^2 + 4*h5*h6 - 2*h5*h8*u^2 - 2*h5*h8*u*v - 2*h5*h8*v + 4*h5*h8 + 2*h5*h9*u*v + 2*h5*h9*u + 2*h5*h9*v + 4*h5*h9 + h6^2*v^2 + 2*h6^2*v + 2*h6^2 - 2*h6*h7*u^2 - 2*h6*h7*u*v - 2*h6*h7*v + 4*h6*h7 + 2*h6*h8*u*v + 2*h6*h8*u + 2*h6*h8*v + 4*h6*h8 + h7*h9*u^2 + 2*h7*h9*u + 2*h7*h9 + h8^2*u^2 + 2*h8^2*u + 2*h8^2

def d3 (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) : ℂ :=
  h0*h4*h7 + 2*h0*h4*h8 + h0*h4*h9 + h0*h5^2 + 2*h0*h5*h6 + 2*h0*h5*h8 + 2*h0*h5*h9 + h0*h6^2 + 2*h0*h6*h7 + 2*h0*h6*h8 + h0*h7*h9 + h0*h8^2 + h1^2*h7 + 2*h1^2*h8 + h1^2*h9 + 2*h1*h2*h5 + 2*h1*h2*h6 + 2*h1*h2*h8 + 2*h1*h2*h9 + 2*h1*h3*h5 + 2*h1*h3*h6 + 2*h1*h3*h7 + 2*h1*h3*h8 - 2*h1*h5*h8*u - 2*h1*h5*h8*v + 2*h1*h5*h8 + 2*h1*h5*h9*v + 2*h1*h5*h9 - 2*h1*h6*h7*u - 2*h1*h6*h7*v + 2*h1*h6*h7 + 2*h1*h6*h8*v + 2*h1*h6*h8 + 2*h1*h7*h9*u + 2*h1*h7*h9 + 2*h1*h8^2*u + 2*h1*h8^2 + h2^2*h4 + 2*h2^2*h6 + h2^2*h9 + 2*h2*h3*h4 + 2*h2*h3*h5 + 2*h2*h3*h6 + 2*h2*h3*h8 - 2*h2*h4*h8*u - 2*h2*h4*h8*v + 2*h2*h4*h8 + 2*h2*h4*h9*v + 2*h2*h4*h9 - 2*h2*h5*h6*u - 2*h2*h5*h6*v + 2*h2*h5*h6 + 2*h2*h5*h9*u + 2*h2*h5*h9 + 2*h2*h6^2*v + 2*h2*h6^2 + 2*h2*h6*h8*u + 2*h2*h6*h8 + h3^2*h4 + 2*h3^2*h5 + h3^2*h7 - 2*h3*h4*h7*u - 2*h3*h4*h7*v + 2*h3*h4*h7 + 2*h3*h4*h8*v + 2*h3*h4*h8 - 2*h3*h5^2*u - 2*h3*h5^2*v + 2*h3*h5^2 + 2*h3*h5*h6*v + 2*h3*h5*h6 + 2*h3*h5*h8*u + 2*h3*h5*h8 + 2*h3*h6*h7*u + 2*h3*h6*h7 + h4*h7*h9 + h4*h8^2 + h5^2*h9 + 2*h5*h6*h8 + h6^2*h7

def d4 (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) : ℂ :=
  h0*h4*h7*h9 + h0*h4*h8^2 + h0*h5^2*h9 + 2*h0*h5*h6*h8 + h0*h6^2*h7 + h1^2*h7*h9 + h1^2*h8^2 + 2*h1*h2*h5*h9 + 2*h1*h2*h6*h8 + 2*h1*h3*h5*h8 + 2*h1*h3*h6*h7 + h2^2*h4*h9 + h2^2*h6^2 + 2*h2*h3*h4*h8 + 2*h2*h3*h5*h6 + h3^2*h4*h7 + h3^2*h5^2

lemma expansion (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v : ℂ) (z : ℂ) : (mat h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v z).permanent =
  24 + z^1 * d1 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v + z^2 * d2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v + z^3 * d3 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v + z^4 * d4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v := by
  rw [perm4]
  simp [mat,Matrix.of_apply,d1,d2,d3,d4] <;> ring

lemma constant_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, 24 + z^1*a + z^2*b + z^3*c + z^4*d = 24) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  refine ⟨?_,?_,?_⟩
  · linear_combination (8*(h 1)-8*(h (-1))-(h 2)+(h (-2)))/12
  · linear_combination (16*(h 1)+16*(h (-1))-(h 2)-(h (-2)))/24
  · linear_combination ((h 2)-(h (-2))-2*(h 1)+2*(h (-1)))/12

theorem maximal (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : ℂ)
    (level : ∀ u v z : ℂ, (mat h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v z).permanent = 24) :
    h0 = 0 ∧ h1 + h2 + h3 = 0 ∧ h4 = 0 ∧ h5 = 0 ∧ h6 = 0 ∧ h7 = 0 ∧ h8 = 0 ∧ h9 = 0 := by
  have co (u v : ℂ) := constant_coefficients (d1 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v) (d2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v) (d3 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v) (d4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v) (fun z => (expansion h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 u v z).symm.trans (level u v z))
  have c0 := (co (0) (0)).1
  have c1 := (co (1) (0)).1
  have c2 := (co (-1) (0)).1
  have c3 := (co (0) (1)).1
  have c4 := (co (0) (-1)).1
  have c5 := (co (1) (1)).1
  simp only [d1] at c0 c1 c2 c3 c4 c5
  have t0 : h4 = h9 := by
    linear_combination (-2/3) * c0 + (5/12) * c1 + (1/4) * c2 + (1/3) * c3 + (-1/3) * c5
  have t1 : h5 = h9 := by
    linear_combination (5/6) * c0 + (-3/8) * c1 + (-1/8) * c2 + (-3/8) * c3 + (-1/8) * c4 + (1/6) * c5
  have t2 : h6 = h9 := by
    linear_combination (1/6) * c0 + (-1/24) * c1 + (-1/8) * c2 + (1/6) * c3 + (-1/6) * c5
  have t3 : h7 = h9 := by
    linear_combination (-2/3) * c0 + (1/3) * c1 + (5/12) * c3 + (1/4) * c4 + (-1/3) * c5
  have t4 : h8 = h9 := by
    linear_combination (1/6) * c0 + (1/6) * c1 + (-1/24) * c3 + (-1/8) * c4 + (-1/6) * c5
  have t5 : h0 = -2*(h1+h2+h3)-9*h9 := by
    linear_combination (-5/6) * c0 + (-1/4) * c1 + (1/4) * c2 + (-1/4) * c3 + (1/4) * c4 + (1) * c5
  have cQ := (co 0 0).2.1
  have cC := (co 0 0).2.2
  simp only [d2,d3,t0,t1,t2,t3,t4,t5] at cQ cC
  have hcube : h9^3 = 0 := by linear_combination (cC - 2*h9*cQ)/96
  have last : h9 = 0 := by by_contra no; exact (pow_ne_zero _ no) hcube
  rw [last] at cQ
  have hsq : (h1+h2+h3)^2 = 0 := by linear_combination cQ/2
  have arms : h1+h2+h3 = 0 := by by_contra no; exact (pow_ne_zero _ no) hsq
  exact ⟨by rw [t5,arms,last]; ring,arms,t0.trans last,t1.trans last,t2.trans last,
    t3.trans last,t4.trans last,last⟩

end SymmetricStarMaximal
