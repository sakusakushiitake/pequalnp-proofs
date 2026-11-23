import Research.ParameterOr
import Research.SideTables

namespace PlaneResearch.SideBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection
open PlaneResearch.InputDegree PlaneResearch.ParameterOr PlaneResearch.SideTables

/-- Apply a verified lower bound for a finite collection of singleton truth tables to
the complete shared multi-output OR problem. -/
theorem lift_tables {n r d : ℕ} (S : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (low : ∀ p ∉ H, degree S p ≤ 2)
    (probes : Fin d → Option (Fin n)) (inputs : Fin n → Table d) (outputs : Fin r → Table d)
    (ix : ∀ p j, (inputs p).getLsbD j.val = decide (probes j = some p ∧ p ∈ H))
    (ox : ∀ i j, (outputs i).getLsbD j.val = decide (∃ a ∈ S i ∩ H, probes j = some a))
    (R T : Finset (Table d)) (raw : ∀ p, inputs p ∈ R) (sur : ∀ v ∈ T, ∃ i, outputs i = v)
    (nz : 0 ∉ T) (b : ℕ)
    (bound : ∀ (gs : List Gate) (w : List (Table d)), FanInTwo ⟨gs,0⟩ → (∀ a ∈ w, a ∈ R) →
      T ⊆ (run gs w).toFinset → b ≤ gs.length)
    (C : Circuit) (o : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (o i)).eval (List.ofFn x) = sumRow (S i) x) :
    b + (∑ i, (((S i \ H).card + min 1 (S i ∩ H).card)-1)) ≤ C.size := by
  obtain ⟨gs,sel,ok,le,ev⟩ := residual_on_singletons S H thin low C o hf hc
  let w := List.ofFn inputs
  have bits (j : Fin d) : w.map (fun a => a.getLsbD j.val) =
      List.ofFn (fun p => decide (probes j = some p ∧ p ∈ H)) := by
    change (List.ofFn inputs).map _ = _
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (fun p => ix p j))
  have got (i : Fin r) : (run gs w).getD (sel i) 0 = outputs i := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have a := wire_bits gs w ⟨j,hj⟩ (sel i) ok
    rw [bits,ev] at a
    exact a.trans (ox i ⟨j,hj⟩).symm
  have all : T ⊆ (run gs w).toFinset := by
    intro v hv
    obtain ⟨i,rfl⟩ := sur v hv
    by_cases h : sel i < (run gs w).length
    · apply List.mem_toFinset.mpr
      rw [←got,List.getD_eq_getElem _ _ h]
      exact List.getElem_mem ..
    · have zero := got i
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)] at zero
      exact (nz (zero ▸ hv)).elim
  have base (a : Table d) (ha : a ∈ w) : a ∈ R := by
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp ha
    exact raw p
  have h := bound gs w ok base all
  omega

end PlaneResearch.SideBridge
