import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case4_0 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [230]=false := by decide +kernel
private theorem case4_1 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [257]=false := by decide +kernel
private theorem case4_2 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [31,185]=false := by decide +kernel
private theorem case4_3 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [31,217]=false := by decide +kernel
private theorem case4_4 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [31,249]=false := by decide +kernel
private theorem case4_5 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [61,155]=false := by decide +kernel
private theorem case4_6 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [61,217]=false := by decide +kernel
private theorem case4_7 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [61,219]=false := by decide +kernel
private theorem case4_8 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [63,217]=false := by decide +kernel
private theorem case4_9 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [93,155]=false := by decide +kernel
private theorem case4_10 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [93,185]=false := by decide +kernel
private theorem case4_11 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [93,187]=false := by decide +kernel
private theorem case4_12 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [95,185]=false := by decide +kernel
private theorem case4_13 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [123,157]=false := by decide +kernel
private theorem case4_14 : branch 113078212145816597093331040047546785012958969400039613319782796884875149312 5 tailRows [125,155]=false := by decide +kernel
theorem reject4 : branch 0 7 (row25::tailRows) [31,246]=false := by
  change solve 113078212145816597093331040047546785012958969400039613319782796884875149312 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case4_0
  · exact case4_1
  · exact case4_2
  · exact case4_3
  · exact case4_4
  · exact case4_5
  · exact case4_6
  · exact case4_7
  · exact case4_8
  · exact case4_9
  · exact case4_10
  · exact case4_11
  · exact case4_12
  · exact case4_13
  · exact case4_14
end PlaneResearch.CompactEightReject
