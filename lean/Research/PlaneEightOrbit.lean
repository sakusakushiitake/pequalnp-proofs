import Research.PlaneSevenOrbit
import Research.PlaneEightOrbitData
import Research.PlaneEight

namespace PlaneResearch.EightOrbit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.PlaneOrderThree (lines)
open PlaneResearch.SevenOrbit (Set13 Points Lower transfer l0 l1 undo0 undo1 image0 image1)

private lemma caseA : Lower sA 24 := by
  intro C o ok hc
  apply PlaneResearch.PlaneEight.eight702.lower C (fun i => o (PlaneResearch.PlaneEight.eight702.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneEight.eight702.labels i ∈ sA) i)

private lemma caseB : Lower sB 24 := by
  intro C o ok hc
  apply PlaneResearch.PlaneSeven.eight468.lower C (fun i => o (PlaneResearch.PlaneSeven.eight468.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneSeven.eight468.labels i ∈ sB) i)

private lemma caseC : Lower sC 24 := by
  intro C o ok hc
  apply PlaneResearch.PlaneEight.eight117.lower C (fun i => o (PlaneResearch.PlaneEight.eight117.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneEight.eight117.labels i ∈ sC) i)

/-- All 1,287 eight-line subsets of PG(2,3) require 24 gates with arbitrary negations. -/
theorem all_eight_sets (s : Set13) (eight : s.card=8) (C : Circuit) (o : Points → ℕ) (hf : FanInTwo C)
    (hc : ∀ i ∈ s, ∀ x, (Circuit.mk C.gates (o i)).eval (List.ofFn x) = sumRow (lines i) x) : 24 ≤ C.size := by
  suffices h : ∀ n (t : Set13), rank t=n → t.card=8 → Lower t 24 from h _ s rfl eight C o hf hc
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro t eq card
    have non : t.Nonempty := Finset.card_pos.mp (by omega)
    rcases step t card with rfl|rfl|rfl|p0|p1
    · exact caseA
    · exact caseB
    · exact caseC
    · apply transfer t non _ _ _ undo0 image0
      have inj : Function.Injective l0 := Function.LeftInverse.injective undo0
      exact ih _ (eq ▸ p0) _ rfl (by simpa [Finset.card_image_of_injective _ inj] using card)
    · apply transfer t non _ _ _ undo1 image1
      have inj : Function.Injective l1 := Function.LeftInverse.injective undo1
      exact ih _ (eq ▸ p1) _ rfl (by simpa [Finset.card_image_of_injective _ inj] using card)

end PlaneResearch.EightOrbit
