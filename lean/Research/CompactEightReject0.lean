import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case0_0 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [230]=false := by decide +kernel
private theorem case0_1 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [257]=false := by decide +kernel
private theorem case0_2 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [31,185]=false := by decide +kernel
private theorem case0_3 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [31,217]=false := by decide +kernel
private theorem case0_4 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [31,249]=false := by decide +kernel
private theorem case0_5 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [61,155]=false := by decide +kernel
private theorem case0_6 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [61,217]=false := by decide +kernel
private theorem case0_7 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [61,219]=false := by decide +kernel
private theorem case0_8 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [63,217]=false := by decide +kernel
private theorem case0_9 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [93,155]=false := by decide +kernel
private theorem case0_10 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [93,185]=false := by decide +kernel
private theorem case0_11 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [93,187]=false := by decide +kernel
private theorem case0_12 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [95,185]=false := by decide +kernel
private theorem case0_13 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [123,157]=false := by decide +kernel
private theorem case0_14 : branch 13803492693581127574869511724554050904902217944340773110325048447598592 6 tailRows [125,155]=false := by decide +kernel
theorem reject0 : branch 0 7 (row25::tailRows) [233]=false := by
  change solve 13803492693581127574869511724554050904902217944340773110325048447598592 6 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case0_0
  · exact case0_1
  · exact case0_2
  · exact case0_3
  · exact case0_4
  · exact case0_5
  · exact case0_6
  · exact case0_7
  · exact case0_8
  · exact case0_9
  · exact case0_10
  · exact case0_11
  · exact case0_12
  · exact case0_13
  · exact case0_14
end PlaneResearch.CompactEightReject
