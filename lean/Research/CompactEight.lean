import Research.CompactEightRow22
import Research.CompactEightRow25
import Research.CompactEightRow44
import Research.CompactEightRow69
import Research.CompactEightRow98
import Research.CompactEightRow138
import Research.CompactEightRow161
import Research.CompactEightRow208
import Research.CompactEightReject

namespace PlaneResearch.CompactEight
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables PlaneResearch.CompactTables
private def choices : RowPlan 9 := [(22,options22),(25,options25),(44,options44),(69,options69),(98,options98),(138,options138),(161,options161),(208,options208)]
private lemma reject : possible 7 ∅ (choices.map Prod.snd) = false := PlaneResearch.CompactEightReject.reject

theorem lower (T : Finset (Table 9)) (sub : T ⊆ U) (must : F ⊆ T) (dis : Disjoint R T)
    (gs : List Gate) (w : List (Table 9)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : T.card+7+1 ≤ gs.length := by
  apply PlaneResearch.CompactTables.lower R T U code choices (by decide) (by decide) dis sub _ _ reject gs w ok raw hit
  · intro v hv
    apply must
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro v hv
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact check22
    · exact check25
    · exact check44
    · exact check69
    · exact check98
    · exact check138
    · exact check161
    · exact check208

end PlaneResearch.CompactEight
