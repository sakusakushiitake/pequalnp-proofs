import Research.PlaneFamilies
import Research.SixRowsOr
import Research.SideCertificates
import Research.SideBridge

namespace PlaneResearch.PlaneSeven
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.InputDegree PlaneResearch.ParameterOr PlaneResearch.SideTables
open PlaneResearch.PlaneOrderThree (lines)

private lemma row4 : ∀ i, (lines i).card = 4 := by decide +kernel
private lemma thin : ∀ i j : Fin 13, i ≠ j → (lines i ∩ lines j).card ≤ 1 := by decide +kernel

theorem all_six (lab : Fin 6 ↪ Fin 13) (C : Circuit) (out : Fin 6 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (lines (lab i)) x) :
    18 ≤ C.size := by
  have h := six_rows (by decide : 6 ≤ 6) (fun i => lines (lab i))
    (fun i j ne => thin _ _ (fun eq => ne (lab.injective eq))) C out hf hc
  simpa [row4] using h

namespace seven234
def labels : Fin 7 → Fin 13 := ![0,1,2,3,4,5,6]
def rows (i : Fin 7) : Finset (Fin 13) := lines (labels i)
def H : Finset (Fin 13) := {1,2,3,4,5,6}
private def probes : Fin 7 → Option (Fin 13) := ![some 1,some 2,some 3,some 4,some 5,some 6,none]
private def inputMask : Fin 13 → Table 7 := ![0,1,2,4,8,16,32,0,0,0,0,0,0]
private def outputMask : Fin 7 → Table 7 := ![5,11,22,44,24,49,34]
theorem lower (C : Circuit) (out : Fin 7 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    21 ≤ C.size := by
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputMask outputMask (by decide +kernel) (by decide +kernel)
    PlaneResearch.SideCertificates.seven234.R PlaneResearch.SideCertificates.seven234.T (by decide +kernel) (by decide +kernel) (by decide)
    11 PlaneResearch.SideCertificates.seven234.lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 10 := by decide +kernel
  simpa only [cost] using h
end seven234

namespace seven936
def labels : Fin 7 → Fin 13 := ![0,1,2,3,4,5,7]
def rows (i : Fin 7) : Finset (Fin 13) := lines (labels i)
def H : Finset (Fin 13) := {1,3,4,5}
theorem lower (C : Circuit) (out : Fin 7 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    21 ≤ C.size := by
  have h := two_high_per_row rows H (by decide +kernel) (by decide +kernel) (by decide +kernel) C out hf hc
  simpa [rows,row4] using h
end seven936

namespace seven468
def labels : Fin 7 → Fin 13 := ![0,1,2,3,4,6,9]
def rows (i : Fin 7) : Finset (Fin 13) := lines (labels i)
def H : Finset (Fin 13) := {2,3,4,5,9}
private def probes : Fin 6 → Option (Fin 13) := ![some 2,some 3,some 4,some 5,some 9,none]
private def inputMask : Fin 13 → Table 6 := ![0,0,1,2,4,8,0,0,0,16,0,0,0]
private def outputMask : Fin 7 → Table 6 := ![18,5,11,6,12,17,24]
theorem lower (C : Circuit) (out : Fin 7 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    21 ≤ C.size := by
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputMask outputMask (by decide +kernel) (by decide +kernel)
    PlaneResearch.SideCertificates.seven468.R PlaneResearch.SideCertificates.seven468.T (by decide +kernel) (by decide +kernel) (by decide)
    8 PlaneResearch.SideCertificates.seven468.lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 13 := by decide +kernel
  simpa only [cost] using h
end seven468

namespace seven78
def labels : Fin 7 → Fin 13 := ![0,1,2,3,4,7,8]
def rows (i : Fin 7) : Finset (Fin 13) := lines (labels i)
def H : Finset (Fin 13) := {3,4}
theorem lower (C : Circuit) (out : Fin 7 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    21 ≤ C.size := by
  have h := two_high_per_row rows H (by decide +kernel) (by decide +kernel) (by decide +kernel) C out hf hc
  simpa [rows,row4] using h
end seven78

namespace eight468
def labels : Fin 8 → Fin 13 := ![0,1,2,3,4,5,7,8]
def rows (i : Fin 8) : Finset (Fin 13) := lines (labels i)
def H : Finset (Fin 13) := {1,3,4,5,8}
private def probes : Fin 6 → Option (Fin 13) := ![some 1,some 3,some 4,some 5,some 8,none]
private def inputMask : Fin 13 → Table 6 := ![0,1,0,2,4,8,0,0,16,0,0,0,0]
private def outputMask : Fin 8 → Table 6 := ![3,5,10,6,12,25,18,20]
theorem lower (C : Circuit) (out : Fin 8 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (rows i) x) :
    24 ≤ C.size := by
  have h := PlaneResearch.SideBridge.lift_tables rows H (by decide +kernel) (by decide +kernel)
    probes inputMask outputMask (by decide +kernel) (by decide +kernel)
    PlaneResearch.SideCertificates.eight468.R PlaneResearch.SideCertificates.eight468.T (by decide +kernel) (by decide +kernel) (by decide)
    9 PlaneResearch.SideCertificates.eight468.lower C out hf hc
  have cost : (∑ i, (((rows i \ H).card + min 1 (rows i ∩ H).card)-1)) = 15 := by decide +kernel
  simpa only [cost] using h
end eight468

end PlaneResearch.PlaneSeven
