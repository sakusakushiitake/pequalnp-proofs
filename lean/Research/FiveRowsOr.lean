import Research.ParameterOr

namespace PlaneResearch.ParameterOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection PlaneResearch.InputDegree

private def through {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => p ∈ S i)

private lemma dual_linear {n m : ℕ} (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) {p q : Fin n} (pq : p ≠ q) :
    (through S p ∩ through S q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra ne
  have hit (a : Fin m) (h : a ∈ through S p ∩ through S q) : p ∈ S a ∧ q ∈ S a :=
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2,(Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2⟩
  exact pq (Finset.card_le_one.mp (thin i j ne) _ (Finset.mem_inter.mpr ⟨(hit i hi).1,(hit j hj).1⟩)
    _ (Finset.mem_inter.mpr ⟨(hit i hi).2,(hit j hj).2⟩))

private lemma shared_at {n m : ℕ} (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) {i : Fin m} {p : Fin n} (pi : p ∈ S i) :
    (shared S i).card ≤ 1 + (m-degree S p) := by
  classical
  let A := (shared S i).erase p
  let B := Finset.univ \ through S p
  have other (a : ↥A) : ∃ j ∈ B, a.val ∈ S j := by
    obtain ⟨na,sa⟩ := Finset.mem_erase.mp a.property
    obtain ⟨ai,j,ji,aj⟩ := Finset.mem_filter.mp sa
    refine ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,aj⟩
    intro h
    exact na (Finset.card_le_one.mp (thin i j ji.symm) _ (Finset.mem_inter.mpr ⟨ai,aj⟩)
      _ (Finset.mem_inter.mpr ⟨pi,(Finset.mem_filter.mp h).2⟩))
  choose j mem aj using other
  let f (a : ↥A) : ↥B := ⟨j a,mem a⟩
  have inj : Function.Injective f := by
    intro a b eq
    have same : j a=j b := congrArg Subtype.val eq
    have outside := (Finset.mem_sdiff.mp (mem b)).2
    have ne : i ≠ j b := by rintro eq; exact outside (eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,pi⟩)
    apply Subtype.ext
    exact Finset.card_le_one.mp (thin i (j b) ne) _
      (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_erase.mp a.property).2).1,same ▸ aj a⟩)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_erase.mp b.property).2).1,aj b⟩)
  have card : A.card ≤ B.card := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
  have bcard : B.card=m-degree S p := by simp [B,through,degree,Finset.card_sdiff_of_subset]
  have erased : (shared S i).card ≤ A.card+1 := by
    by_cases h : p ∈ shared S i
    · simp [A,Finset.card_erase_of_mem h]; have := Finset.card_pos.mpr (show (shared S i).Nonempty from ⟨p,h⟩); omega
    · simp [A,Finset.erase_eq_of_notMem h]
  omega

/-- Every linear family on at most five rows, of unbounded size, has its separate-tree
cost even against unrestricted negation. -/
theorem five_rows {n m : ℕ} (small : m ≤ 5) (S : Fin m → Finset (Fin n))
    (two : ∀ i, 2 ≤ (S i).card) (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size := by
  classical
  let H := Finset.univ.filter (fun p => 3 ≤ degree S p)
  by_cases one : ∀ i, (S i ∩ H).card ≤ 1
  · exact one_high_per_row S H thin (fun p hp => by
      have : ¬ 3 ≤ degree S p := fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      omega) one C out hf hc
  push_neg at one
  obtain ⟨i,big⟩ := one
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp big
  have h (a : Fin n) (ha : a ∈ S i ∩ H) : 3 ≤ (through S a).card :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
  have cp := h p hp
  have cq := h q hq
  have meet := dual_linear S thin ne
  have count := Finset.card_union_add_card_inter (through S p) (through S q)
  have all : through S p ∪ through S q = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  apply three_shared S two thin _ C out hf hc
  intro j
  have contained : j ∈ through S p ∪ through S q := all ▸ Finset.mem_univ j
  rcases Finset.mem_union.mp contained with jh|jh
  · have v := shared_at S thin (Finset.mem_filter.mp jh).2
    change 3 ≤ degree S p at cp
    omega
  · have v := shared_at S thin (Finset.mem_filter.mp jh).2
    change 3 ≤ degree S q at cq
    omega

end PlaneResearch.ParameterOr
