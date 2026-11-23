import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case3_0 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [230]=false := by decide +kernel
private theorem case3_1 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [257]=false := by decide +kernel
private theorem case3_2 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [31,185]=false := by decide +kernel
private theorem case3_3 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [31,217]=false := by decide +kernel
private theorem case3_4 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [31,249]=false := by decide +kernel
private theorem case3_5 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [61,155]=false := by decide +kernel
private theorem case3_6 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [61,217]=false := by decide +kernel
private theorem case3_7 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [61,219]=false := by decide +kernel
private theorem case3_8 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [63,217]=false := by decide +kernel
private theorem case3_9 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [93,155]=false := by decide +kernel
private theorem case3_10 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [93,185]=false := by decide +kernel
private theorem case3_11 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [93,187]=false := by decide +kernel
private theorem case3_12 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [95,185]=false := by decide +kernel
private theorem case3_13 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [123,157]=false := by decide +kernel
private theorem case3_14 : branch 26328072917139296674479506920917608079723773850137277815725228032 5 tailRows [125,155]=false := by decide +kernel
theorem reject3 : branch 0 7 (row25::tailRows) [31,214]=false := by
  change solve 26328072917139296674479506920917608079723773850137277815725228032 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case3_0
  · exact case3_1
  · exact case3_2
  · exact case3_3
  · exact case3_4
  · exact case3_5
  · exact case3_6
  · exact case3_7
  · exact case3_8
  · exact case3_9
  · exact case3_10
  · exact case3_11
  · exact case3_12
  · exact case3_13
  · exact case3_14
end PlaneResearch.CompactEightReject
