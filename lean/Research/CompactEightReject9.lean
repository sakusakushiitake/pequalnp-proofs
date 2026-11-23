import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case9_0 : branch 365375409332725729551075950683981427448345526272 5 tailRows [230]=false := by decide +kernel
private theorem case9_1 : branch 365375409332725729551075950683981427448345526272 5 tailRows [257]=false := by decide +kernel
private theorem case9_2 : branch 365375409332725729551075950683981427448345526272 5 tailRows [31,185]=false := by decide +kernel
private theorem case9_3 : branch 365375409332725729551075950683981427448345526272 5 tailRows [31,217]=false := by decide +kernel
private theorem case9_4 : branch 365375409332725729551075950683981427448345526272 5 tailRows [31,249]=false := by decide +kernel
private theorem case9_5 : branch 365375409332725729551075950683981427448345526272 5 tailRows [61,155]=false := by decide +kernel
private theorem case9_6 : branch 365375409332725729551075950683981427448345526272 5 tailRows [61,217]=false := by decide +kernel
private theorem case9_7 : branch 365375409332725729551075950683981427448345526272 5 tailRows [61,219]=false := by decide +kernel
private theorem case9_8 : branch 365375409332725729551075950683981427448345526272 5 tailRows [63,217]=false := by decide +kernel
private theorem case9_9 : branch 365375409332725729551075950683981427448345526272 5 tailRows [93,155]=false := by decide +kernel
private theorem case9_10 : branch 365375409332725729551075950683981427448345526272 5 tailRows [93,185]=false := by decide +kernel
private theorem case9_11 : branch 365375409332725729551075950683981427448345526272 5 tailRows [93,187]=false := by decide +kernel
private theorem case9_12 : branch 365375409332725729551075950683981427448345526272 5 tailRows [95,185]=false := by decide +kernel
private theorem case9_13 : branch 365375409332725729551075950683981427448345526272 5 tailRows [123,157]=false := by decide +kernel
private theorem case9_14 : branch 365375409332725729551075950683981427448345526272 5 tailRows [125,155]=false := by decide +kernel
theorem reject9 : branch 0 7 (row25::tailRows) [87,158]=false := by
  change solve 365375409332725729551075950683981427448345526272 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case9_0
  · exact case9_1
  · exact case9_2
  · exact case9_3
  · exact case9_4
  · exact case9_5
  · exact case9_6
  · exact case9_7
  · exact case9_8
  · exact case9_9
  · exact case9_10
  · exact case9_11
  · exact case9_12
  · exact case9_13
  · exact case9_14
end PlaneResearch.CompactEightReject
