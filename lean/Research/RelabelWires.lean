import Research.StarOwners

namespace PlaneResearch.RelabelWires
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.TripleSystems

def index {n : ℕ} (σ : Fin n → Fin n) (i : ℕ) : ℕ := if hi : i<n then (σ ⟨i,hi⟩).val else i
def gateMap {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (index σ)⟩
def rename {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gateMap σ),index σ C.output⟩

theorem size_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : (rename σ C).size=C.size := by
  simp [rename,Circuit.size]

private lemma before {n : ℕ} (σ : Fin n → Fin n) (i k : ℕ) : index σ i<n+k ↔ i<n+k := by
  by_cases h : i<n
  · simp only [index,dif_pos h]
    have := (σ ⟨i,h⟩).isLt
    omega
  · simp [index,h]

/-- Relabel raw inputs while keeping every gate and its operation, even in
circuits with repeated or out-of-range predecessor references. -/
theorem wire {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    W (rename σ C) (index σ i) x = W C i (fun p => x (σ p)) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases raw : i<n
    · let p : Fin n := ⟨i,raw⟩
      change W (rename σ C) (index σ p.val) x = W C p.val _
      rw [show index σ p.val=(σ p).val from dif_pos raw,input,input]
    · rw [show index σ i=i from dif_neg raw]
      by_cases valid : i<n+C.gates.length
      · let k := i-n
        have hk : k<C.gates.length := by dsimp [k]; omega
        have hk' : k<(rename σ C).gates.length := by simpa [rename] using hk
        have eq : i=n+k := by dsimp [k]; omega
        rw [eq,gate (rename σ C) k hk',gate C k hk]
        simp only [rename,List.getElem_map,gateMap,List.map_map,Function.comp_apply]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases prev : j<n+k
        · simp only [Function.comp_apply,if_pos ((before σ j k).mpr prev),if_pos prev]
          simpa only [rename] using ih j (by omega)
        · simp [show ¬index σ j<n+k from fun h => prev ((before σ j k).mp h),prev]
      · change (wiresFrom (rename σ C).gates (List.ofFn x)).getD i false =
          (wiresFrom C.gates (List.ofFn (fun p => x (σ p)))).getD i false
        have outside : n + C.gates.length ≤ i := Nat.le_of_not_lt valid
        rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom,rename] using outside),
          List.getD_eq_default _ _ (by simpa [length_wiresFrom] using outside)]

theorem gate_wire {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    W (rename σ C) (n+k) x = W C (n+k) (fun p => x (σ p)) := by
  simpa [index,show ¬ n+k<n from by omega] using wire σ C x (n+k)

theorem eval {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn x) = C.eval (List.ofFn (fun p => x (σ p))) :=
  wire σ C x C.output

end PlaneResearch.RelabelWires
