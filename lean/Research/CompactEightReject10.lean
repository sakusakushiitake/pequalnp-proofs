import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case10_0 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [230]=false := by decide +kernel
private theorem case10_1 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [257]=false := by decide +kernel
private theorem case10_2 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [31,185]=false := by decide +kernel
private theorem case10_3 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [31,217]=false := by decide +kernel
private theorem case10_4 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [31,249]=false := by decide +kernel
private theorem case10_5 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [61,155]=false := by decide +kernel
private theorem case10_6 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [61,217]=false := by decide +kernel
private theorem case10_7 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [61,219]=false := by decide +kernel
private theorem case10_8 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [63,217]=false := by decide +kernel
private theorem case10_9 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [93,155]=false := by decide +kernel
private theorem case10_10 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [93,185]=false := by decide +kernel
private theorem case10_11 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [93,187]=false := by decide +kernel
private theorem case10_12 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [95,185]=false := by decide +kernel
private theorem case10_13 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [123,157]=false := by decide +kernel
private theorem case10_14 : branch 1569275433846670190958947355802071346530499533650371018752 5 tailRows [125,155]=false := by decide +kernel
theorem reject10 : branch 0 7 (row25::tailRows) [87,190]=false := by
  change solve 1569275433846670190958947355802071346530499533650371018752 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case10_0
  · exact case10_1
  · exact case10_2
  · exact case10_3
  · exact case10_4
  · exact case10_5
  · exact case10_6
  · exact case10_7
  · exact case10_8
  · exact case10_9
  · exact case10_10
  · exact case10_11
  · exact case10_12
  · exact case10_13
  · exact case10_14
end PlaneResearch.CompactEightReject
