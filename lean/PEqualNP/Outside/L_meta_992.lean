import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_992_aux

open Matrix MvPolynomial

abbrev V (F : Type) := Fin 3 → F

lemma uniqueLine {F : Type} [Field F] {p q u v : V F}
    (hp : p ≠ 0) (hpq : ∀ c : F, q ≠ c • p) (hu : u ≠ 0)
    (hpu : p ⬝ᵥ u = 0) (hqu : q ⬝ᵥ u = 0)
    (hpv : p ⬝ᵥ v = 0) (hqv : q ⬝ᵥ v = 0) : ∃ c : F, v = c • u := by
  have hc : crossProduct p q ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2
    ((LinearIndependent.pair_iff' hp).2 fun c => (hpq c).symm)
  have par (z : V F) (a : p ⬝ᵥ z = 0) (b : q ⬝ᵥ z = 0) :
      ∃ c : F, c • crossProduct p q = z := by
    by_contra! h
    have hn := crossProduct_ne_zero_iff_linearIndependent.2
      ((LinearIndependent.pair_iff' hc).2 h)
    apply hn
    simpa only [cross_cross_eq_smul_sub_smul, a, b, zero_smul, sub_zero]
  obtain ⟨c, ce⟩ := par u hpu hqu
  obtain ⟨d, de⟩ := par v hpv hqv
  have cn : c ≠ 0 := by rintro rfl; exact hu (by simpa using ce.symm)
  exact ⟨d / c, by rw [← ce, ← de, smul_smul, div_mul_cancel₀ _ cn]⟩

noncomputable def form {F : Type} [Field F] (p : V F) : MvPolynomial (Fin 3) F :=
  ∑ t, C (p t) * X t

lemma formHom {F : Type} [Field F] (p : V F) : (form p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _

lemma formEval {F : Type} [Field F] (p z : V F) : eval z (form p) = p ⬝ᵥ z := by
  simp [form, dotProduct]

lemma interpolation {F : Type} [Field F] {k b : ℕ} (l : Fin k → V F)
    (P : Fin k → MvPolynomial (Fin 3) F) (hom : ∀ i, (P i).IsHomogeneous b)
    (diag : ∀ i, eval (l i) (P i) ≠ 0)
    (off : ∀ i j, i ≠ j → eval (l j) (P i) = 0) : 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  let D := (Finset.univ : Finset (Fin 3)).finsuppAntidiag b
  let A : Matrix (Fin k) D F := fun i d => (P i).coeff d.val
  let B : Matrix D (Fin k) F := fun d j => ∏ t, l j t ^ d.val t
  have he (i j : Fin k) : (A * B) i j = eval (l j) (P i) := by
    rw [Matrix.mul_apply, eval_eq']
    change (∑ d : D, (P i).coeff d.val * ∏ t, l j t ^ d.val t) = _
    rw [Finset.sum_coe_sort D (fun d : Fin 3 →₀ ℕ => (P i).coeff d * ∏ t, l j t ^ d t)]
    symm
    apply Finset.sum_subset
    · intro d hd
      have hsum := (hom i).degree_eq_sum_deg_support hd
      apply Finset.mem_finsuppAntidiag.mpr
      exact ⟨(Finset.sum_subset (Finset.subset_univ _) (by
        intro t _ ht
        simpa using ht)).symm.trans hsum.symm, Finset.subset_univ _⟩
    · intro d _ hd
      simp [notMem_support_iff.mp hd]
  have eqd : A * B = Matrix.diagonal (fun i => eval (l i) (P i)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [he]
    · simp [he, Matrix.diagonal_apply, hij, off i j hij]
  have hr := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  rw [eqd, Matrix.rank_diagonal] at hr
  have hc : Fintype.card {i : Fin k // eval (l i) (P i) ≠ 0} = k := by
    simp [Fintype.card_subtype, diag]
  rw [hc] at hr
  have hD : Fintype.card D = (b + 2).choose 2 := by
    change Fintype.card (↑((Finset.univ : Finset (Fin 3)).finsuppAntidiag b)) = _
    rw [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show 3 + b - 1 = b + 2 by omega]
    exact Nat.choose_symm_of_eq_add rfl
  rw [hD, Nat.choose_two_right] at hr
  have hb : b + 2 - 1 = b + 1 := by omega
  rw [hb, Nat.mul_comm (b + 2)] at hr
  omega

lemma upper {F : Type} [Field F] {n k b : ℕ} (pt : Fin n → V F) (l : Fin k → V F)
    (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool)
    (hp : ∀ p, pt p ≠ 0) (hpp : ∀ p q, p ≠ q → ∀ c : F, pt q ≠ c • pt p)
    (hl : ∀ i, l i ≠ 0) (hll : ∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hc : ∀ i, (y i).card ≤ b) (hn : ∀ i, ∀ p ∈ y i, pt p ⬝ᵥ l i ≠ 0)
    (safe : ∀ i x, g x = true → ∃ p, x p = true ∧ pt p ⬝ᵥ l i = 0)
    (two : ∀ i, ∃ p q, p ≠ q ∧ pt p ⬝ᵥ l i = 0 ∧ pt q ⬝ᵥ l i = 0 ∧
      g (fun v => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v => decide (v ∈ y i ∨ v = q)) = true) : 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  have crossHit (i j : Fin k) (ij : i ≠ j) : ∃ v ∈ y i, pt v ⬝ᵥ l j = 0 := by
    by_contra! miss
    obtain ⟨p, q, pq, pi, qi, gp, gq⟩ := two i
    have hit (a : Fin n) (ga : g (fun v => decide (v ∈ y i ∨ v = a)) = true) :
        pt a ⬝ᵥ l j = 0 := by
      obtain ⟨v, hv, zv⟩ := safe j _ ga
      rcases of_decide_eq_true hv with hv | rfl
      · exact (miss v hv zv).elim
      · exact zv
    obtain ⟨c, eq⟩ := uniqueLine (hp p) (hpp p q pq) (hl i) pi qi (hit p gp) (hit q gq)
    exact hll i j ij c eq
  have non (i : Fin k) : ∃ j, l i j ≠ 0 := by
    by_contra! h
    exact hl i (funext h)
  choose j hj using non
  let P (i : Fin k) : MvPolynomial (Fin 3) F :=
    (X (j i)) ^ (b - (y i).card) * ∏ p ∈ y i, form (pt p)
  apply interpolation l P
  · intro i
    have h := IsHomogeneous.prod (y i) (fun p => form (pt p)) (fun _ => 1) (fun p _ => formHom (pt p))
    have h' : (∏ p ∈ y i, form (pt p)).IsHomogeneous (y i).card := by simpa using h
    have hh := (isHomogeneous_X_pow (R := F) (j i) (b - (y i).card)).mul h'
    simpa [P, Nat.sub_add_cancel (hc i)] using hh
  · intro i
    simp only [P, map_mul, map_pow, eval_X, map_prod, formEval]
    exact mul_ne_zero (pow_ne_zero _ (hj _)) (Finset.prod_ne_zero_iff.mpr (hn i))
  · intro i r hir
    obtain ⟨v, hv, zv⟩ := crossHit i r hir
    simp only [P, map_mul, map_pow, eval_X, map_prod, formEval]
    rw [Finset.prod_eq_zero hv zv, mul_zero]

end PEqualNP.Outside.L_meta_992_aux

theorem PEqualNP.Outside.L_meta_992 : ¬ (∃ (F : Type) (_ : Field F) (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ (b + 1) * (b + 2) < 2 * k) := by
  rintro ⟨F, inst, n, k, b, pt, l, y, g, hp, hp', hl, hl', hy, hoff, hsafe, hw, hlt⟩
  let _ : Field F := inst
  exact (Nat.not_lt_of_ge (PEqualNP.Outside.L_meta_992_aux.upper pt l y g hp hp' hl hl' hy hoff hsafe hw)) hlt
