import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case12_0 : branch 365375409333058036549867437147296706679053221888 5 tailRows [230]=false := by decide +kernel
private theorem case12_1 : branch 365375409333058036549867437147296706679053221888 5 tailRows [257]=false := by decide +kernel
private theorem case12_2 : branch 365375409333058036549867437147296706679053221888 5 tailRows [31,185]=false := by decide +kernel
private theorem case12_3 : branch 365375409333058036549867437147296706679053221888 5 tailRows [31,217]=false := by decide +kernel
private theorem case12_4 : branch 365375409333058036549867437147296706679053221888 5 tailRows [31,249]=false := by decide +kernel
private theorem case12_5 : branch 365375409333058036549867437147296706679053221888 5 tailRows [61,155]=false := by decide +kernel
private theorem case12_6 : branch 365375409333058036549867437147296706679053221888 5 tailRows [61,217]=false := by decide +kernel
private theorem case12_7 : branch 365375409333058036549867437147296706679053221888 5 tailRows [61,219]=false := by decide +kernel
private theorem case12_8 : branch 365375409333058036549867437147296706679053221888 5 tailRows [63,217]=false := by decide +kernel
private theorem case12_9 : branch 365375409333058036549867437147296706679053221888 5 tailRows [93,155]=false := by decide +kernel
private theorem case12_10 : branch 365375409333058036549867437147296706679053221888 5 tailRows [93,185]=false := by decide +kernel
private theorem case12_11 : branch 365375409333058036549867437147296706679053221888 5 tailRows [93,187]=false := by decide +kernel
private theorem case12_12 : branch 365375409333058036549867437147296706679053221888 5 tailRows [95,185]=false := by decide +kernel
private theorem case12_13 : branch 365375409333058036549867437147296706679053221888 5 tailRows [123,157]=false := by decide +kernel
private theorem case12_14 : branch 365375409333058036549867437147296706679053221888 5 tailRows [125,155]=false := by decide +kernel
theorem reject12 : branch 0 7 (row25::tailRows) [118,158]=false := by
  change solve 365375409333058036549867437147296706679053221888 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case12_0
  · exact case12_1
  · exact case12_2
  · exact case12_3
  · exact case12_4
  · exact case12_5
  · exact case12_6
  · exact case12_7
  · exact case12_8
  · exact case12_9
  · exact case12_10
  · exact case12_11
  · exact case12_12
  · exact case12_13
  · exact case12_14
end PlaneResearch.CompactEightReject
