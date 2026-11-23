import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case7_0 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [230]=false := by decide +kernel
private theorem case7_1 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [257]=false := by decide +kernel
private theorem case7_2 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [31,185]=false := by decide +kernel
private theorem case7_3 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [31,217]=false := by decide +kernel
private theorem case7_4 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [31,249]=false := by decide +kernel
private theorem case7_5 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [61,155]=false := by decide +kernel
private theorem case7_6 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [61,217]=false := by decide +kernel
private theorem case7_7 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [61,219]=false := by decide +kernel
private theorem case7_8 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [63,217]=false := by decide +kernel
private theorem case7_9 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [93,155]=false := by decide +kernel
private theorem case7_10 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [93,185]=false := by decide +kernel
private theorem case7_11 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [93,187]=false := by decide +kernel
private theorem case7_12 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [95,185]=false := by decide +kernel
private theorem case7_13 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [123,157]=false := by decide +kernel
private theorem case7_14 : branch 52656145834278593348959013841835216159447547704886241645582876672 5 tailRows [125,155]=false := by decide +kernel
theorem reject7 : branch 0 7 (row25::tailRows) [62,215]=false := by
  change solve 52656145834278593348959013841835216159447547704886241645582876672 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case7_0
  · exact case7_1
  · exact case7_2
  · exact case7_3
  · exact case7_4
  · exact case7_5
  · exact case7_6
  · exact case7_7
  · exact case7_8
  · exact case7_9
  · exact case7_10
  · exact case7_11
  · exact case7_12
  · exact case7_13
  · exact case7_14
end PlaneResearch.CompactEightReject
