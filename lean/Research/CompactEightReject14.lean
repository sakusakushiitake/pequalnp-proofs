import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case14_0 : branch 365375409333390343548813666115522658444123308032 5 tailRows [230]=false := by decide +kernel
private theorem case14_1 : branch 365375409333390343548813666115522658444123308032 5 tailRows [257]=false := by decide +kernel
private theorem case14_2 : branch 365375409333390343548813666115522658444123308032 5 tailRows [31,185]=false := by decide +kernel
private theorem case14_3 : branch 365375409333390343548813666115522658444123308032 5 tailRows [31,217]=false := by decide +kernel
private theorem case14_4 : branch 365375409333390343548813666115522658444123308032 5 tailRows [31,249]=false := by decide +kernel
private theorem case14_5 : branch 365375409333390343548813666115522658444123308032 5 tailRows [61,155]=false := by decide +kernel
private theorem case14_6 : branch 365375409333390343548813666115522658444123308032 5 tailRows [61,217]=false := by decide +kernel
private theorem case14_7 : branch 365375409333390343548813666115522658444123308032 5 tailRows [61,219]=false := by decide +kernel
private theorem case14_8 : branch 365375409333390343548813666115522658444123308032 5 tailRows [63,217]=false := by decide +kernel
private theorem case14_9 : branch 365375409333390343548813666115522658444123308032 5 tailRows [93,155]=false := by decide +kernel
private theorem case14_10 : branch 365375409333390343548813666115522658444123308032 5 tailRows [93,185]=false := by decide +kernel
private theorem case14_11 : branch 365375409333390343548813666115522658444123308032 5 tailRows [93,187]=false := by decide +kernel
private theorem case14_12 : branch 365375409333390343548813666115522658444123308032 5 tailRows [95,185]=false := by decide +kernel
private theorem case14_13 : branch 365375409333390343548813666115522658444123308032 5 tailRows [123,157]=false := by decide +kernel
private theorem case14_14 : branch 365375409333390343548813666115522658444123308032 5 tailRows [125,155]=false := by decide +kernel
theorem reject14 : branch 0 7 (row25::tailRows) [119,158]=false := by
  change solve 365375409333390343548813666115522658444123308032 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case14_0
  · exact case14_1
  · exact case14_2
  · exact case14_3
  · exact case14_4
  · exact case14_5
  · exact case14_6
  · exact case14_7
  · exact case14_8
  · exact case14_9
  · exact case14_10
  · exact case14_11
  · exact case14_12
  · exact case14_13
  · exact case14_14
end PlaneResearch.CompactEightReject
