import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case5_0 : branch 154742509522358552789778432 5 tailRows [230]=false := by decide +kernel
private theorem case5_1 : branch 154742509522358552789778432 5 tailRows [257]=false := by decide +kernel
private theorem case5_2 : branch 154742509522358552789778432 5 tailRows [31,185]=false := by decide +kernel
private theorem case5_3 : branch 154742509522358552789778432 5 tailRows [31,217]=false := by decide +kernel
private theorem case5_4 : branch 154742509522358552789778432 5 tailRows [31,249]=false := by decide +kernel
private theorem case5_5 : branch 154742509522358552789778432 5 tailRows [61,155]=false := by decide +kernel
private theorem case5_6 : branch 154742509522358552789778432 5 tailRows [61,217]=false := by decide +kernel
private theorem case5_7 : branch 154742509522358552789778432 5 tailRows [61,219]=false := by decide +kernel
private theorem case5_8 : branch 154742509522358552789778432 5 tailRows [63,217]=false := by decide +kernel
private theorem case5_9 : branch 154742509522358552789778432 5 tailRows [93,155]=false := by decide +kernel
private theorem case5_10 : branch 154742509522358552789778432 5 tailRows [93,185]=false := by decide +kernel
private theorem case5_11 : branch 154742509522358552789778432 5 tailRows [93,187]=false := by decide +kernel
private theorem case5_12 : branch 154742509522358552789778432 5 tailRows [95,185]=false := by decide +kernel
private theorem case5_13 : branch 154742509522358552789778432 5 tailRows [123,157]=false := by decide +kernel
private theorem case5_14 : branch 154742509522358552789778432 5 tailRows [125,155]=false := by decide +kernel
theorem reject5 : branch 0 7 (row25::tailRows) [62,87]=false := by
  change solve 154742509522358552789778432 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case5_0
  · exact case5_1
  · exact case5_2
  · exact case5_3
  · exact case5_4
  · exact case5_5
  · exact case5_6
  · exact case5_7
  · exact case5_8
  · exact case5_9
  · exact case5_10
  · exact case5_11
  · exact case5_12
  · exact case5_13
  · exact case5_14
end PlaneResearch.CompactEightReject
