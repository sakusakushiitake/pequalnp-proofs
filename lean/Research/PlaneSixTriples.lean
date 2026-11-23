import Research.CompactSix
import Research.SideBridge
import Research.PlaneSeven

namespace PlaneResearch.PlaneSixTriples
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.InputDegree PlaneResearch.ParameterOr PlaneResearch.SideTables
open PlaneResearch.PlaneOrderThree (lines)

namespace eight702
def labels : Fin 8 → Fin 13 := ![0,1,2,3,4,5,6,7]
def rows (i : Fin 8) : Finset (Fin 13) := lines (labels i)
private def H : Finset (Fin 13) := {1,2,3,4,5,6,7}
private def T : Finset (Table 8) := {5,11,22,44,49,68,88,98}
private def probes : Fin 8 → Option (Fin 13) := ![some 1,some 2,some 3,some 4,some 5,some 6,some 7,none]
private def inputs : Fin 13 → Table 8 := ![0,1,2,4,8,16,32,64,0,0,0,0,0]
private def outputs : Fin 8 → Table 8 := ![5,11,22,44,88,49,98,68]

theorem lower (C : Circuit) (out : Fin 8 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    24 ≤ C.size := by
  have lower := PlaneResearch.CompactSix.lower T (by decide) (by decide) (by decide)
  have exactCard : T.card+5+1 = 14 := by decide
  simp only [exactCard] at lower
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputs outputs (by decide +kernel) (by decide +kernel)
    PlaneResearch.CompactSix.R T (by decide +kernel) (by decide +kernel) (by decide)
    14 lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 10 := by decide +kernel
  simpa only [cost] using h
end eight702

namespace nine234
def labels : Fin 9 → Fin 13 := ![0,1,2,3,4,5,6,7,11]
def rows (i : Fin 9) : Finset (Fin 13) := lines (labels i)
private def H : Finset (Fin 13) := {1,2,3,4,5,6,7}
private def T : Finset (Table 8) := {5,11,22,44,49,65,68,88,98}
private def probes : Fin 8 → Option (Fin 13) := ![some 1,some 2,some 3,some 4,some 5,some 6,some 7,none]
private def inputs : Fin 13 → Table 8 := ![0,1,2,4,8,16,32,64,0,0,0,0,0]
private def outputs : Fin 9 → Table 8 := ![5,11,22,44,88,49,98,68,65]

theorem lower (C : Circuit) (out : Fin 9 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    27 ≤ C.size := by
  have lower := PlaneResearch.CompactSix.lower T (by decide) (by decide) (by decide)
  have exactCard : T.card+5+1 = 15 := by decide
  simp only [exactCard] at lower
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputs outputs (by decide +kernel) (by decide +kernel)
    PlaneResearch.CompactSix.R T (by decide +kernel) (by decide +kernel) (by decide)
    15 lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 12 := by decide +kernel
  simpa only [cost] using h
end nine234

end PlaneResearch.PlaneSixTriples
