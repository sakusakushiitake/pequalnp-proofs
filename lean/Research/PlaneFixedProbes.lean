import Research.PlaneClean
import Research.CleanProbeFamily

namespace PlaneResearch.PlaneFixedProbes
open PlaneResearch.PlaneClean PlaneResearch.CleanProbeFamily
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners
abbrev V := Fin 26
private instance : DecidableRel graph.Adj := fun p q => inferInstanceAs (Decidable (adjacent p q))
def F : Finset (Finset V) := {{0,1,2,3,6,7,17,18},{0,2,3,4,9,10,15,21},{2,8,13,15,16,17,22,23},{4,7,13,14,16,17,21,24},{6,10,13,14,15,18,22,24},{0,1,7,8,9,10,23,24},{0,1,2,4,5,6,9,11,12,19},{0,1,3,4,5,8,10,11,12,20},{0,3,5,6,7,8,9,11,12,25},{5,13,14,15,16,18,19,20,23,25},{11,13,14,17,19,20,21,22,23,25},{12,13,16,18,19,20,21,22,24,25},{1,3,9,14,16,22}}
theorem count : F.card=13 := by decide +kernel
theorem independent : ∀ S ∈ F, Independent graph S := by
  simp only [F,Finset.mem_insert,Finset.mem_singleton]
  intro S h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Independent <;> decide +kernel
theorem covers : Covers graph F := by
  unfold Covers
  decide +kernel

theorem test_iff (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (two : ∀ g ∈ C.gates, g.inputs.length≤2) :
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ S ∈ F, W C (26+k) (indicator S)=false) ↔
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ x : V → Bool, W C (26+k) x=true →
      ∃ p q, graph.Adj p q ∧ x p=true ∧ x q=true) :=
  sufficient (by decide) graph F independent covers C ops two

end PlaneResearch.PlaneFixedProbes
