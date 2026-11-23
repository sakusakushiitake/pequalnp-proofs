import Research.CompactEightRejectOne0
import Research.CompactEightRejectOne1
import Research.CompactEightRejectOne2

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem reject1 : branch 0 7 (row25::tailRows) [256]=false := by
  change solve 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case1_0
  · exact case1_1
  · exact case1_2
  · exact case1_3
  · exact case1_4
  · exact case1_5
  · exact case1_6
  · exact case1_7
  · exact case1_8
  · exact case1_9
  · exact case1_10
  · exact case1_11
  · exact case1_12
  · exact case1_13
  · exact case1_14
end PlaneResearch.CompactEightReject
