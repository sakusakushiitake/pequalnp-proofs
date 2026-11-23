import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case13_0 : branch 730750818665783766100788645326367461593036357632 5 tailRows [230]=false := by decide +kernel
private theorem case13_1 : branch 730750818665783766100788645326367461593036357632 5 tailRows [257]=false := by decide +kernel
private theorem case13_2 : branch 730750818665783766100788645326367461593036357632 5 tailRows [31,185]=false := by decide +kernel
private theorem case13_3 : branch 730750818665783766100788645326367461593036357632 5 tailRows [31,217]=false := by decide +kernel
private theorem case13_4 : branch 730750818665783766100788645326367461593036357632 5 tailRows [31,249]=false := by decide +kernel
private theorem case13_5 : branch 730750818665783766100788645326367461593036357632 5 tailRows [61,155]=false := by decide +kernel
private theorem case13_6 : branch 730750818665783766100788645326367461593036357632 5 tailRows [61,217]=false := by decide +kernel
private theorem case13_7 : branch 730750818665783766100788645326367461593036357632 5 tailRows [61,219]=false := by decide +kernel
private theorem case13_8 : branch 730750818665783766100788645326367461593036357632 5 tailRows [63,217]=false := by decide +kernel
private theorem case13_9 : branch 730750818665783766100788645326367461593036357632 5 tailRows [93,155]=false := by decide +kernel
private theorem case13_10 : branch 730750818665783766100788645326367461593036357632 5 tailRows [93,185]=false := by decide +kernel
private theorem case13_11 : branch 730750818665783766100788645326367461593036357632 5 tailRows [93,187]=false := by decide +kernel
private theorem case13_12 : branch 730750818665783766100788645326367461593036357632 5 tailRows [95,185]=false := by decide +kernel
private theorem case13_13 : branch 730750818665783766100788645326367461593036357632 5 tailRows [123,157]=false := by decide +kernel
private theorem case13_14 : branch 730750818665783766100788645326367461593036357632 5 tailRows [125,155]=false := by decide +kernel
theorem reject13 : branch 0 7 (row25::tailRows) [118,159]=false := by
  change solve 730750818665783766100788645326367461593036357632 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case13_0
  · exact case13_1
  · exact case13_2
  · exact case13_3
  · exact case13_4
  · exact case13_5
  · exact case13_6
  · exact case13_7
  · exact case13_8
  · exact case13_9
  · exact case13_10
  · exact case13_11
  · exact case13_12
  · exact case13_13
  · exact case13_14
end PlaneResearch.CompactEightReject
