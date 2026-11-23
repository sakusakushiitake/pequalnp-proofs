import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case6_0 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [230]=false := by decide +kernel
private theorem case6_1 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [257]=false := by decide +kernel
private theorem case6_2 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [31,185]=false := by decide +kernel
private theorem case6_3 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [31,217]=false := by decide +kernel
private theorem case6_4 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [31,249]=false := by decide +kernel
private theorem case6_5 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [61,155]=false := by decide +kernel
private theorem case6_6 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [61,217]=false := by decide +kernel
private theorem case6_7 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [61,219]=false := by decide +kernel
private theorem case6_8 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [63,217]=false := by decide +kernel
private theorem case6_9 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [93,155]=false := by decide +kernel
private theorem case6_10 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [93,185]=false := by decide +kernel
private theorem case6_11 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [93,187]=false := by decide +kernel
private theorem case6_12 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [95,185]=false := by decide +kernel
private theorem case6_13 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [123,157]=false := by decide +kernel
private theorem case6_14 : branch 26328072917139296674479506920917608079723773854748963832005132288 5 tailRows [125,155]=false := by decide +kernel
theorem reject6 : branch 0 7 (row25::tailRows) [62,214]=false := by
  change solve 26328072917139296674479506920917608079723773854748963832005132288 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case6_0
  · exact case6_1
  · exact case6_2
  · exact case6_3
  · exact case6_4
  · exact case6_5
  · exact case6_6
  · exact case6_7
  · exact case6_8
  · exact case6_9
  · exact case6_10
  · exact case6_11
  · exact case6_12
  · exact case6_13
  · exact case6_14
end PlaneResearch.CompactEightReject
