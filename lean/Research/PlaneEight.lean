import Research.PlaneSixTriples
import Research.CompactEight
import Research.SideBridge
import Research.PlaneSeven

namespace PlaneResearch.PlaneEight
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.InputDegree PlaneResearch.ParameterOr PlaneResearch.SideTables
open PlaneResearch.PlaneOrderThree (lines)

namespace eight702
abbrev labels := PlaneResearch.PlaneSixTriples.eight702.labels
abbrev rows := PlaneResearch.PlaneSixTriples.eight702.rows
theorem lower (C : Circuit) (out : Fin 8 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    24 ≤ C.size := PlaneResearch.PlaneSixTriples.eight702.lower C out hf hc
end eight702

namespace nine234
abbrev labels := PlaneResearch.PlaneSixTriples.nine234.labels
abbrev rows := PlaneResearch.PlaneSixTriples.nine234.rows
theorem lower (C : Circuit) (out : Fin 9 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    27 ≤ C.size := PlaneResearch.PlaneSixTriples.nine234.lower C out hf hc
end nine234

namespace eight117
def labels : Fin 8 → Fin 13 := ![0,1,2,3,4,6,9,10]
def rows (i : Fin 8) : Finset (Fin 13) := lines (labels i)
private def H : Finset (Fin 13) := {0,2,3,4,5,6,9,10}
private def T : Finset (Table 9) := {22,25,44,69,98,138,161,208}
private def probes : Fin 9 → Option (Fin 13) := ![some 0,some 2,some 3,some 4,some 5,some 6,some 9,some 10,none]
private def inputs : Fin 13 → Table 9 := ![1,0,2,4,8,16,32,0,0,64,128,0,0]
private def outputs : Fin 8 → Table 9 := ![69,138,22,44,25,98,208,161]

theorem lower (C : Circuit) (out : Fin 8 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    24 ≤ C.size := by
  have lower := PlaneResearch.CompactEight.lower T (by decide) (by decide) (by decide)
  have exactCard : T.card+7+1 = 16 := by decide
  simp only [exactCard] at lower
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputs outputs (by decide +kernel) (by decide +kernel)
    PlaneResearch.CompactEight.R T (by decide +kernel) (by decide +kernel) (by decide)
    16 lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 8 := by decide +kernel
  simpa only [cost] using h
end eight117

end PlaneResearch.PlaneEight
