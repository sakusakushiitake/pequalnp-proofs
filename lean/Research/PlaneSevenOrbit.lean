import Research.PlaneOrbitData
import Research.PlaneSeven

namespace PlaneResearch.SevenOrbit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.PlaneOrderThree (lines)

def Lower (s : Set13) (b : ℕ := 21) : Prop :=
  ∀ (C : Circuit) (o : Points → ℕ), FanInTwo C →
    (∀ i ∈ s, ∀ x, (Circuit.mk C.gates (o i)).eval (List.ofFn x) = sumRow (lines i) x) → b ≤ C.size

private lemma rename_sum (a : Set13) (p : Points → Points) (x : Points → Bool) :
    sumRow a (fun j => x (p j)) = sumRow (a.image p) x := by
  simp only [sumRow,decide_eq_decide]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact ⟨p j,Finset.mem_image.mpr ⟨j,hj,rfl⟩,hv⟩
  · rintro ⟨v,hv,hit⟩
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨j,hj,hit⟩

theorem transfer {b : ℕ} (s : Set13) (non : s.Nonempty) (p l inv : Points → Points)
    (undo : ∀ i, inv (l i)=i) (col : ∀ i, (lines i).image p=lines (l i))
    (parent : Lower (s.image l) b) : Lower s b := by
  classical
  intro C o hf hc
  obtain ⟨j0,h0⟩ := non
  let pick (i : Points) := if inv i ∈ s then inv i else j0
  have valid (i : Points) : pick i ∈ s := by dsimp [pick]; split <;> assumption
  let σ (j : Points) : Bool ⊕ Points := .inr (p j)
  have ev (i : Points) (x : Points → Bool) :
      (Circuit.mk C.gates (o (pick i))).eval (List.ofFn (assignInput σ x)) = sumRow (lines (l (pick i))) x := by
    rw [hc _ (valid i)]
    change sumRow (lines (pick i)) (fun j => x (p j)) = _
    rw [rename_sum,col]
  have live (i : Points) : (lines i).Nonempty := (by decide +kernel : ∀ i, (lines i).Nonempty) i
  obtain ⟨gs,os,ok,sm,hew,_⟩ := specialize_outputs σ C.gates (fun i => o (pick i)) hf (fun i => by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    simp only [ev]
    simpa [sumRow,Finset.Nonempty] using live (l (pick i)))
  have h := parent ⟨gs,0⟩ os ok (by
    intro i hi x
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    have id : pick (l v)=v := by simp [pick,undo,hv]
    simpa only [id] using (hew (l v) x).trans (ev (l v) x))
  exact h.trans sm

private lemma A : Lower sA := by
  intro C o ok hc
  apply PlaneResearch.PlaneSeven.seven234.lower C (fun i => o (PlaneResearch.PlaneSeven.seven234.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneSeven.seven234.labels i ∈ sA) i)

private lemma B : Lower sB := by
  intro C o ok hc
  apply PlaneResearch.PlaneSeven.seven936.lower C (fun i => o (PlaneResearch.PlaneSeven.seven936.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneSeven.seven936.labels i ∈ sB) i)

private lemma Ccase : Lower sC := by
  intro C o ok hc
  apply PlaneResearch.PlaneSeven.seven468.lower C (fun i => o (PlaneResearch.PlaneSeven.seven468.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneSeven.seven468.labels i ∈ sC) i)

private lemma D : Lower sD := by
  intro C o ok hc
  apply PlaneResearch.PlaneSeven.seven78.lower C (fun i => o (PlaneResearch.PlaneSeven.seven78.labels i)) ok
  exact fun i => hc _ ((by decide +kernel : ∀ i, PlaneResearch.PlaneSeven.seven78.labels i ∈ sD) i)

/-- All 1,716 seven-line subsets of PG(2,3) require 21 gates with arbitrary negations. -/
theorem all_seven_sets (s : Set13) (seven : s.card=7) (C : Circuit) (o : Points → ℕ) (hf : FanInTwo C)
    (hc : ∀ i ∈ s, ∀ x, (Circuit.mk C.gates (o i)).eval (List.ofFn x) = sumRow (lines i) x) : 21 ≤ C.size := by
  suffices h : ∀ l (s : Set13), rank s=l → s.card=7 → Lower s from h _ s rfl seven C o hf hc
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro t eq card
    have non : t.Nonempty := Finset.card_pos.mp (by omega)
    rcases step t card with rfl|rfl|rfl|rfl|p0|p1
    · exact A
    · exact B
    · exact Ccase
    · exact D
    · apply transfer t non _ _ _ undo0 image0
      have inj : Function.Injective l0 := Function.LeftInverse.injective undo0
      exact ih _ (eq ▸ p0) _ rfl (by simpa [Finset.card_image_of_injective _ inj] using card)
    · apply transfer t non _ _ _ undo1 image1
      have inj : Function.Injective l1 := Function.LeftInverse.injective undo1
      exact ih _ (eq ▸ p1) _ rfl (by simpa [Finset.card_image_of_injective _ inj] using card)

end PlaneResearch.SevenOrbit
