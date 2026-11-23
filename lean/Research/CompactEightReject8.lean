import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case8_0 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [230]=false := by decide +kernel
private theorem case8_1 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [257]=false := by decide +kernel
private theorem case8_2 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [31,185]=false := by decide +kernel
private theorem case8_3 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [31,217]=false := by decide +kernel
private theorem case8_4 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [31,249]=false := by decide +kernel
private theorem case8_5 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [61,155]=false := by decide +kernel
private theorem case8_6 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [61,217]=false := by decide +kernel
private theorem case8_7 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [61,219]=false := by decide +kernel
private theorem case8_8 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [63,217]=false := by decide +kernel
private theorem case8_9 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [93,155]=false := by decide +kernel
private theorem case8_10 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [93,185]=false := by decide +kernel
private theorem case8_11 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [93,187]=false := by decide +kernel
private theorem case8_12 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [95,185]=false := by decide +kernel
private theorem case8_13 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [123,157]=false := by decide +kernel
private theorem case8_14 : branch 26328072917139296674479506920917608079723773859360649850432520192 5 tailRows [125,155]=false := by decide +kernel
theorem reject8 : branch 0 7 (row25::tailRows) [63,214]=false := by
  change solve 26328072917139296674479506920917608079723773859360649850432520192 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case8_0
  · exact case8_1
  · exact case8_2
  · exact case8_3
  · exact case8_4
  · exact case8_5
  · exact case8_6
  · exact case8_7
  · exact case8_8
  · exact case8_9
  · exact case8_10
  · exact case8_11
  · exact case8_12
  · exact case8_13
  · exact case8_14
end PlaneResearch.CompactEightReject
