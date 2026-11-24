import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1504 :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (t : Fin N → (Fin N → Bool) → Bool), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ l0 : Fin N, Monotone (t l0)) → (∀ (x y : Fin N → Bool), (∀ l1 : Fin N, (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) → (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) → ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true) → (∀ p4 l4 : Fin N, I p4 l4 → ∃ l5 : Fin N, decide (l5 = l4) = true ∧ t l5 (fun k4 : Fin N => decide (k4 = p4)) = true) → ∀ (l6 : Fin N) (z : Fin N → Bool), (∀ l7 : Fin N, (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) → (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) := by
  intro N I _ t _ mono sound covers line z arc
  constructor
  · intro h
    obtain ⟨p, j, incident, present, selected⟩ :=
      sound z (fun k => decide (k = line)) arc ⟨line, by simp, h⟩
    have eq : j = line := of_decide_eq_true selected
    exact ⟨p, eq ▸ incident, present⟩
  · rintro ⟨p, incident, present⟩
    obtain ⟨j, selected, fired⟩ := covers p line incident
    have eq : j = line := of_decide_eq_true selected
    subst j
    have included : (fun k : Fin N => decide (k = p)) ≤ z := by
      intro k
      by_cases hk : k = p
      · subst k
        simp [present]
      · simp [hk]
    have step := mono line included
    exact (Bool.le_iff_imp.mp step) fired
