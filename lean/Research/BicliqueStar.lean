import Mathlib

namespace PlaneResearch.BicliqueStar

variable {V : Type*} [DecidableEq V]

def NoSquare (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d

theorem bipartite_is_star (G : SimpleGraph V) (hG : NoSquare G) (A B : Finset V)
    (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! h
  obtain ⟨a,ha,c,hc,hac⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b,hb,d,hd,hbd⟩ := Finset.one_lt_card.mp h.2
  exact (hG a b c d (cross _ ha _ hb) (cross _ hc _ hb).symm (cross _ hc _ hd)
    (cross _ ha _ hd).symm).elim hac hbd

theorem one_center (G : SimpleGraph V) (hG : NoSquare G) (A B : Finset V)
    (ha : A.Nonempty) (hb : B.Nonempty) (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ c : V, ∀ a ∈ A, ∀ b ∈ B, a = c ∨ b = c := by
  rcases bipartite_is_star G hG A B cross with size|size
  · obtain ⟨c,hc⟩ := ha
    exact ⟨c,fun _ hx _ _ => Or.inl (Finset.card_le_one.mp size _ hx _ hc)⟩
  · obtain ⟨c,hc⟩ := hb
    exact ⟨c,fun _ _ _ hx => Or.inr (Finset.card_le_one.mp size _ hx _ hc)⟩

theorem cover_by_centers {m : ℕ} (G : SimpleGraph V) (hG : NoSquare G)
    (A B : Fin m → Finset V) (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (cross : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, G.Adj a b)
    (cover : ∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) :
    ∃ T : Finset V, T.card ≤ m ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  classical
  choose c hc using fun i => one_center G hG (A i) (B i) (ha i) (hb i) (cross i)
  refine ⟨Finset.univ.image c,by simpa using Finset.card_image_le (s:=Finset.univ) (f:=c),?_⟩
  intro u v huv
  obtain ⟨i,h|h⟩ := cover u v huv
  · rcases hc i u h.1 v h.2 with e|e
    · exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  · rcases hc i v h.1 u h.2 with e|e
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    · exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)

theorem binary_cone_card (inputs gates outputs : Finset ℕ)
    (parents : ℕ → Finset ℕ) (arity : ∀ j ∈ gates, (parents j).card ≤ 2)
    (disjoint : Disjoint inputs gates)
    (uses : ∀ w ∈ inputs ∪ gates, w ∈ outputs ∨ ∃ j ∈ gates, w ∈ parents j) :
    inputs.card ≤ gates.card + outputs.card := by
  have sub : inputs ∪ gates ⊆ outputs ∪ gates.biUnion parents := by
    intro w hw
    exact Finset.mem_union.mpr ((uses w hw).imp_right (fun h => Finset.mem_biUnion.mpr h))
  have upper : (gates.biUnion parents).card ≤ ∑ j ∈ gates, (parents j).card :=
    Finset.card_biUnion_le
  have bound : (∑ j ∈ gates, (parents j).card) ≤ ∑ _j ∈ gates, 2 := Finset.sum_le_sum arity
  have all := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  rw [Finset.card_union_of_disjoint disjoint] at all
  simp at bound
  omega

end PlaneResearch.BicliqueStar
