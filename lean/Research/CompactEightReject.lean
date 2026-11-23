import Research.CompactEightReject0
import Research.CompactEightReject1
import Research.CompactEightReject2
import Research.CompactEightReject3
import Research.CompactEightReject4
import Research.CompactEightReject5
import Research.CompactEightReject6
import Research.CompactEightReject7
import Research.CompactEightReject8
import Research.CompactEightReject9
import Research.CompactEightReject10
import Research.CompactEightReject11
import Research.CompactEightReject12
import Research.CompactEightReject13
import Research.CompactEightReject14

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
theorem reject : possible 7 ∅ [options22,options25,options44,options69,options98,options138,options161,options208]=false := by
  have eq : rawRows.map (List.map List.toFinset) = [options22,options25,options44,options69,options98,options138,options161,options208] := by decide +kernel
  rw [←eq]
  apply certifies
  apply reject_cons
  intro e he
  simp only [row22,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact reject0
  · exact reject1
  · exact reject2
  · exact reject3
  · exact reject4
  · exact reject5
  · exact reject6
  · exact reject7
  · exact reject8
  · exact reject9
  · exact reject10
  · exact reject11
  · exact reject12
  · exact reject13
  · exact reject14
end PlaneResearch.CompactEightReject
