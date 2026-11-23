import Research.ShardFourUpper

namespace PlaneResearch.ShardFour
open PEqualNP.CircuitLowerBounds
private def choices : Finset ℕ := {0xaaa8a880,0xe888a888,0xe888e880,0xe8a8a880,0xe8a8c880,0xe8a8e800,0xeaa8c080,0xeaaac000,0xeac8e000,0xaaa8a888}
private theorem membership : ∀ i, table i ∈ choices := by decide +kernel
private lemma get {t : ℕ} (h : t ∈ choices) : ∃ i, t=table i := by
  simp only [choices,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩

abbrev Allowed (gs : List Gate) := ∀ g ∈ gs, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2
abbrev One (gs : List Gate) := ∀ i j : Fin gs.length, (gs.get i).op=.not → (gs.get j).op=.not → i=j
abbrev Replacement (t : ℕ) (gs : List Gate) :=
  ∃ gs' : List Gate, ∃ o' : ℕ, Mon gs' ∧ gs'.length≤gs.length ∧ Computes t gs' o'

theorem exact_bounded_search :
    (¬ (∀ T ∈ ({0xaaa8a880, 0xe888a888, 0xe888e880, 0xe8a8a880, 0xe8a8c880, 0xe8a8e800, 0xeaa8c080, 0xeaaac000, 0xeac8e000, 0xaaa8a888} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0))) ↔ ∃ (i : Fin 10) (gs : List Gate) (o : ℕ),
      Allowed gs ∧ One gs ∧ Computes (table i) gs o ∧ gs.length<bound i ∧ ¬Replacement (table i) gs := by
  classical
  change (¬∀ t ∈ choices, ∀ gs o, Allowed gs → One gs → Computes t gs o → Replacement t gs) ↔ _
  constructor
  · intro fail
    by_contra none
    apply fail
    intro t ht gs o allowed one computes
    obtain ⟨i,rfl⟩ := get ht
    by_contra bad
    have short : gs.length<bound i := by
      by_contra! large
      exact bad (large_has_replacement i gs large)
    exact none ⟨i,gs,o,allowed,one,computes,short,bad⟩
  · rintro ⟨i,gs,o,allowed,one,computes,_,bad⟩ universal
    exact bad (universal (table i) (membership i) gs o allowed one computes)

end PlaneResearch.ShardFour
