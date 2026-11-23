import Research.ProjectedOr
import Research.MeasuredOr

namespace PlaneResearch.Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem rank_excess {n m : ℕ} (S : Fin m → Finset (Fin n)) (two : ∀ i, 2 ≤ (S i).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size + ((∑ i, ((S i).card-3))-1) := by
  classical
  have correct (i) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).getD (out i) false = true ↔ ∃ p ∈ S i, x p=true := by
    change (Circuit.mk C.gates (out i)).eval (List.ofFn x) = true ↔ _
    rw [hc]; simp [sumRow]
  by_cases hn : ∃ k : Fin C.gates.length, (C.gates.get k).op = .not
  · have base := (PlaneResearch.TripleSystems.Unrestricted.unrestricted_rows n m S two thin C out hf correct).2 hn
    have unit (i : Fin m) : (S i).card-1 = (1 + if 3 ≤ (S i).card then 1 else 0) + ((S i).card-3) := by
      have := two i
      split <;> omega
    have cost : (∑ i, ((S i).card-1)) = m + (Finset.univ.filter (fun i => 3 ≤ (S i).card)).card +
        (∑ i, ((S i).card-3)) := by
      simp_rw [unit]
      simp [Finset.sum_add_distrib,←Finset.sum_filter]
    rw [cost]
    omega
  · have pos (k : Fin C.gates.length) : (C.gates.get k).op ≠ .not := fun h => hn ⟨k,h⟩
    have full := PlaneResearch.ConeSemantics.monotone_linear_rows S thin C out hf pos correct
    omega

/-- The possible saving is at most one less than the total excess number of
shared points above three per row, truncated at zero. -/
theorem shared_excess {n m : ℕ} (S : Fin m → Finset (Fin n)) (two : ∀ i, 2 ≤ (S i).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size + ((∑ i, ((shared S i).card-3))-1) := by
  classical
  have choose_core (i : Fin m) : ∃ B, shared S i ⊆ B ∧ B ⊆ S i ∧ B.card = max (shared S i).card (min 3 (S i).card) := by
    have subset : shared S i ⊆ S i := Finset.filter_subset ..
    exact Finset.exists_subsuperset_card_eq subset
      (le_max_left ..) (max_le (Finset.card_le_card subset) (min_le_right ..))
  choose R keep sub card using choose_core
  let E (i : Fin m) := S i \ R i
  let U := Finset.univ.biUnion E
  have exclusive (i j : Fin m) {p} (h : p ∈ E i) (sj : p ∈ S j) : j = i := by
    by_contra ne
    obtain ⟨si,no⟩ := Finset.mem_sdiff.mp h
    exact no (keep i (Finset.mem_filter.mpr ⟨si,j,ne,sj⟩))
  have residual (i) : S i \ U = R i := by
    ext p
    constructor
    · intro h
      obtain ⟨si,nu⟩ := Finset.mem_sdiff.mp h
      by_contra nr
      exact nu (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨si,nr⟩⟩)
    · intro ri
      refine Finset.mem_sdiff.mpr ⟨sub i ri,?_⟩
      intro inU
      obtain ⟨j,_,ej⟩ := Finset.mem_biUnion.mp inU
      have eq := exclusive j i ej (sub i ri)
      subst j
      exact (Finset.mem_sdiff.mp ej).2 ri
  have touch (p) (h : p ∈ U) : ∃ i, p ∈ S i := by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨i,(Finset.mem_sdiff.mp hi).1⟩
  have rem (i) : 2 ≤ (S i \ U).card := by rw [residual,card]; exact (le_min (by decide) (two i)).trans (le_max_right ..)
  have d : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint E := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro p pi pj
    exact ne (exclusive j i pj (Finset.mem_sdiff.mp pi).1)
  have count : U.card = ∑ i, ((S i).card - (R i).card) := by
    rw [show U = Finset.univ.biUnion E from rfl, Finset.card_biUnion d]
    exact Finset.sum_congr rfl (fun i _ => Finset.card_sdiff_of_subset (sub i))

  have sR (i) : 2 ≤ (R i).card := by simpa only [residual] using rem i
  have non (i) : (S i \ U).Nonempty := Finset.card_pos.mp (by have := rem i; omega)
  obtain ⟨gs,o,sz,ok,ev⟩ := project_or_rows U S touch non C.gates out hf hc
  let D : Circuit := ⟨gs,0⟩
  have thinR (i j : Fin m) (ne : i ≠ j) : (R i ∩ R j).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ne)
  have er (i) (x : Fin n → Bool) : (Circuit.mk D.gates (o i)).eval (List.ofFn x) = sumRow (R i) x :=
    (ev i x).trans (congrArg (fun A => sumRow A x) (residual i))
  have bound := rank_excess R sR thinR D o ok er
  have sc (i) : (R i).card-3 = (shared S i).card-3 := by rw [card]; omega
  simp_rw [sc] at bound
  have point (i) : (S i).card-1 = ((S i).card-(R i).card) + ((R i).card-1) := by
    have := sR i
    have := Finset.card_le_card (sub i)
    omega
  have cost : (∑ i, ((S i).card-1)) = U.card + ∑ i, ((R i).card-1) := by
    simp_rw [point]
    rw [Finset.sum_add_distrib,count]
  rw [cost]
  change _ ≤ gs.length + _ at bound
  change _ ≤ C.gates.length + _
  omega

end PlaneResearch.Projection
