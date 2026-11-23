import Research.ShardFourDesk
import PEqualNP.MetaComplexity.Helpers.Support

namespace PlaneResearch.ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def function (i : Fin 10) (x : Fin 5 → Bool) :=
  Nat.testBit (table i) (∑ j : Fin 5, if x j then 2^j.val else 0)
private def fromCode (z : Fin 32) (j : Fin 5) := z.val.testBit j.val
private theorem sensitive : ∀ (i : Fin 10) (j : Fin 5), ∃ z : Fin 32,
    function i (Function.update (fromCode z) j (!(fromCode z j))) ≠ function i (fromCode z) := by
  decide +kernel

theorem four_needed (i : Fin 10) (gs : List Gate) (o : ℕ) (ok : Allowed gs)
    (computes : Computes (table i) gs o) : 4≤gs.length := by
  have size : HasCircuitSize 5 (function i) gs.length := ⟨⟨gs,o⟩,fun g hg => ok g hg,le_rfl,computes⟩
  have dep (j : Fin 5) : ∃ x : Fin 5 → Bool, function i (Function.update x j (!(x j))) ≠ function i x := by
    obtain ⟨z,h⟩ := sensitive i j
    exact ⟨fromCode z,h⟩
  have := PEqualNP.MetaComplexity.Helpers.dep_lower 5 (function i) dep gs.length size
  omega

theorem exclude_seventh (gs : List Gate) (o : ℕ) (ok : Allowed gs)
    (computes : Computes (table 7) gs o) : Replacement (table 7) gs :=
  large_has_replacement 7 gs (four_needed 7 gs o ok computes)

end PlaneResearch.ShardFour
