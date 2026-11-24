import Mathlib

namespace PlaneCylinder

variable {α : Type*} [Fintype α] [DecidableEq α]

def cylinder (free : Finset α) (fixed : α → Bool) : Finset (α → Bool) :=
  Fintype.piFinset fun i => if i ∈ free then Finset.univ else {fixed i}

theorem mem_cylinder (free : Finset α) (fixed x : α → Bool) :
    x ∈ cylinder free fixed ↔ ∀ i, i ∉ free → x i = fixed i := by
  rw [cylinder,Fintype.mem_piFinset]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ free <;> simp_all

theorem card_cylinder (free : Finset α) (fixed : α → Bool) :
    (cylinder free fixed).card = 2 ^ free.card := by
  rw [cylinder,Fintype.card_piFinset]
  calc
    _ = ∏ i : α, (if i ∈ free then 2 else 1 : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ free <;> simp [hi]
    _ = _ := by simp

private theorem split_union (p q : Prop) : (p ∨ q) ↔ (p ∨ ¬p ∧ q) := by tauto

theorem count (T M : Finset α) (inside : T ⊆ M) :
    (Finset.univ.filter (fun x : α → Bool =>
      (∃ t ∈ T, x t = true) ∨ ∀ v ∉ M, x v = true)).card =
      (2 ^ Fintype.card α - 2 ^ (Fintype.card α - T.card)) + 2 ^ (M.card - T.card) := by
  classical
  let A := Finset.univ.filter (fun x : α → Bool => ∃ t ∈ T, x t = true)
  let D := cylinder Tᶜ (fun _ => false)
  let E := cylinder (M \ T) (fun i => decide (i ∉ M))
  have hd : D = Aᶜ := by
    ext x
    simp [D,A,mem_cylinder]
  have he (x : α → Bool) : x ∈ E ↔ x ∉ A ∧ ∀ v ∉ M, x v = true := by
    rw [show E=cylinder (M \ T) (fun i => decide (i ∉ M)) from rfl,mem_cylinder]
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,not_exists,not_and,
      Bool.not_eq_true,Finset.mem_sdiff]
    constructor
    · intro h
      refine ⟨fun i hi => ?_,fun i hi => ?_⟩
      · simpa [inside hi] using h i (by tauto)
      · simpa [hi] using h i (by tauto)
    · rintro ⟨ht,hm⟩ i hi
      by_cases im : i ∈ M
      · have it : i ∈ T := by tauto
        simpa [im] using ht i it
      · simpa [im] using hm i im
  have ca : A.card = 2 ^ Fintype.card α - 2 ^ (Fintype.card α - T.card) := by
    have h := Finset.card_compl_add_card A
    rw [← hd,show D.card = 2 ^ Tᶜ.card from card_cylinder _ _,Finset.card_compl,Fintype.card_fun] at h
    simp only [Fintype.card_bool] at h
    omega
  have ce : E.card = 2 ^ (M.card - T.card) := by
    rw [show E.card = 2 ^ (M \ T).card from card_cylinder _ _,Finset.card_sdiff_of_subset inside]
  have hu : Finset.univ.filter (fun x : α → Bool =>
      (∃ t ∈ T, x t = true) ∨ ∀ v ∉ M, x v = true) = A ∪ E := by
    ext x
    rw [Finset.mem_union,he]
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    exact split_union _ _
  have dis : Disjoint A E := Finset.disjoint_left.mpr fun x ha hx => ((he x).mp hx).1 ha
  rw [hu,Finset.card_union_of_disjoint dis,ca,ce]

omit [Fintype α] in
theorem complement_test (T M D : Finset α) (separate : T ⊆ D → D = M) :
    (∃ t ∈ T, decide (t ∉ D) = true) ∨ ∀ v ∉ M, decide (v ∉ D) = true := by
  by_cases h : T ⊆ D
  · have eq := separate h
    subst D
    exact Or.inr (by simp)
  · obtain ⟨i,it,id⟩ := Finset.not_subset.mp h
    exact Or.inl ⟨i,it,by simp [id]⟩

end PlaneCylinder
