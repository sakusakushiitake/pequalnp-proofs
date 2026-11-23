import Research.ParameterOr

namespace PlaneResearch.ParameterOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection PlaneResearch.InputDegree

/-- Two different shared points in a row meet disjoint sets of other rows. -/
theorem count_high_in_row {n m : ℕ} (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (i : Fin m) :
    2 * (S i ∩ (Finset.univ.filter (fun p => 3 ≤ degree S p))).card ≤ m-1 := by
  classical
  let K := S i ∩ (Finset.univ.filter (fun p => 3 ≤ degree S p))
  let D (p : Fin n) := (Finset.univ.filter (fun j => p ∈ S j)).erase i
  have two (p : Fin n) (hp : p ∈ K) : 2 ≤ (D p).card := by
    obtain ⟨hit,high⟩ := Finset.mem_inter.mp hp
    have three := (Finset.mem_filter.mp high).2
    have hi : i ∈ Finset.univ.filter (fun j => p ∈ S j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    change 2 ≤ ((Finset.univ.filter (fun j => p ∈ S j)).erase i).card
    rw [Finset.card_erase_of_mem hi]
    change 3 ≤ (Finset.univ.filter (fun j => p ∈ S j)).card at three
    omega
  have dis : Set.PairwiseDisjoint (K : Set (Fin n)) D := by
    intro p hp q hq ne
    rw [Function.onFun,Finset.disjoint_left]
    intro j jp jq
    obtain ⟨ji,pj⟩ := Finset.mem_erase.mp jp
    obtain ⟨_,qj⟩ := Finset.mem_erase.mp jq
    exact ne (Finset.card_le_one.mp (thin i j ji.symm)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1,(Finset.mem_filter.mp pj).2⟩)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq).1,(Finset.mem_filter.mp qj).2⟩))
  have range : K.biUnion D ⊆ Finset.univ.erase i := by
    intro j hj
    obtain ⟨p,_,jp⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp jp).1,Finset.mem_univ _⟩
  have size := Finset.card_le_card range
  rw [Finset.card_biUnion dis] at size
  have count := Finset.sum_le_sum two
  change 2 * K.card ≤ m-1
  simpa [Nat.mul_comm] using count.trans size

theorem six_rows {n m : ℕ} (few : m ≤ 6) (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size := by
  classical
  let H := Finset.univ.filter (fun p => 3 ≤ degree S p)
  apply two_high_per_row S H thin _ _ C out hf hc
  · intro p hp
    have notHigh : ¬ 3 ≤ degree S p := fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    omega
  · intro i
    have bound := count_high_in_row S thin i
    change 2 * (S i ∩ H).card ≤ m-1 at bound
    omega

end PlaneResearch.ParameterOr
