import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case11_0 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [230]=false := by decide +kernel
private theorem case11_1 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [257]=false := by decide +kernel
private theorem case11_2 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [31,185]=false := by decide +kernel
private theorem case11_3 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [31,217]=false := by decide +kernel
private theorem case11_4 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [31,249]=false := by decide +kernel
private theorem case11_5 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [61,155]=false := by decide +kernel
private theorem case11_6 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [61,217]=false := by decide +kernel
private theorem case11_7 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [61,219]=false := by decide +kernel
private theorem case11_8 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [63,217]=false := by decide +kernel
private theorem case11_9 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [93,155]=false := by decide +kernel
private theorem case11_10 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [93,185]=false := by decide +kernel
private theorem case11_11 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [93,187]=false := by decide +kernel
private theorem case11_12 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [95,185]=false := by decide +kernel
private theorem case11_13 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [123,157]=false := by decide +kernel
private theorem case11_14 : branch 12259964326927110866866776237009514097515997375854804992 5 tailRows [125,155]=false := by decide +kernel
theorem reject11 : branch 0 7 (row25::tailRows) [94,183]=false := by
  change solve 12259964326927110866866776237009514097515997375854804992 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case11_0
  · exact case11_1
  · exact case11_2
  · exact case11_3
  · exact case11_4
  · exact case11_5
  · exact case11_6
  · exact case11_7
  · exact case11_8
  · exact case11_9
  · exact case11_10
  · exact case11_11
  · exact case11_12
  · exact case11_13
  · exact case11_14
end PlaneResearch.CompactEightReject
