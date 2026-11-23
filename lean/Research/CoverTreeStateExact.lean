import Research.CoverTreeForcedUpper
import PEqualNP.Outside.L_pcx_109

namespace CoverTreeResearch
variable {n t : ℕ} {G : SimpleGraph (Fin n)}

-- The lower bound is k-sandhu's accepted matching potential, L-pcx-109.
-- Querying distinct neighbors of false vertices first attains it at every safe state.
theorem matching_state_exact (miss : Uncovered G t)
    (deg : ∀ a b d, G.Adj a b → G.Adj a d → b=d) (s : State n) (safe : NoBad G s) :
    let r := t-(ones s).card
    let b := (pending G s).card
    optimum (cover_feasible miss) s + 1 = min r b + 2^(r-b+1) := by
  let r := t-(ones s).card
  let b := (pending G s).card
  let L := optimum (cover_feasible miss) s
  change L+1=min r b+2^(r-b+1)
  have lower := PEqualNP.Outside.L_pcx_109.matching_lower deg (t:=t) (N:=optimum (cover_feasible miss))
    (optimum_valid (cover_feasible miss)) s (fun u v e ⟨hu,hv⟩ => safe ⟨u,v,e,hu,hv⟩)
  change PEqualNP.Outside.L_pcx_109.matchPot b r ≤ L at lower
  have upper : L+1 ≤ min r b+2^(r-b+1) := pending_upper miss s
  apply Nat.le_antisymm upper
  by_cases small : b<r
  · rw [min_eq_right (Nat.le_of_lt small)]
    simp only [PEqualNP.Outside.L_pcx_109.matchPot,if_pos small] at lower
    have p : 1≤2^(r-b+1) := Nat.one_le_two_pow
    omega
  · have le : r≤b := by omega
    simp only [PEqualNP.Outside.L_pcx_109.matchPot,if_neg small] at lower
    simp [min_eq_left le,Nat.sub_eq_zero_of_le le]
    omega

end CoverTreeResearch
