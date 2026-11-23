import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
private theorem case2_0 : branch 332306998946228968225951767217569792 5 tailRows [230]=false := by decide +kernel
private theorem case2_1 : branch 332306998946228968225951767217569792 5 tailRows [257]=false := by decide +kernel
private theorem case2_2 : branch 332306998946228968225951767217569792 5 tailRows [31,185]=false := by decide +kernel
private theorem case2_3 : branch 332306998946228968225951767217569792 5 tailRows [31,217]=false := by decide +kernel
private theorem case2_4 : branch 332306998946228968225951767217569792 5 tailRows [31,249]=false := by decide +kernel
private theorem case2_5 : branch 332306998946228968225951767217569792 5 tailRows [61,155]=false := by decide +kernel
private theorem case2_6 : branch 332306998946228968225951767217569792 5 tailRows [61,217]=false := by decide +kernel
private theorem case2_7 : branch 332306998946228968225951767217569792 5 tailRows [61,219]=false := by decide +kernel
private theorem case2_8 : branch 332306998946228968225951767217569792 5 tailRows [63,217]=false := by decide +kernel
private theorem case2_9 : branch 332306998946228968225951767217569792 5 tailRows [93,155]=false := by decide +kernel
private theorem case2_10 : branch 332306998946228968225951767217569792 5 tailRows [93,185]=false := by decide +kernel
private theorem case2_11 : branch 332306998946228968225951767217569792 5 tailRows [93,187]=false := by decide +kernel
private theorem case2_12 : branch 332306998946228968225951767217569792 5 tailRows [95,185]=false := by decide +kernel
private theorem case2_13 : branch 332306998946228968225951767217569792 5 tailRows [123,157]=false := by decide +kernel
private theorem case2_14 : branch 332306998946228968225951767217569792 5 tailRows [125,155]=false := by decide +kernel
theorem reject2 : branch 0 7 (row25::tailRows) [31,118]=false := by
  change solve 332306998946228968225951767217569792 5 (row25::tailRows)=false
  apply reject_cons
  intro e he
  simp only [row25,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case2_0
  · exact case2_1
  · exact case2_2
  · exact case2_3
  · exact case2_4
  · exact case2_5
  · exact case2_6
  · exact case2_7
  · exact case2_8
  · exact case2_9
  · exact case2_10
  · exact case2_11
  · exact case2_12
  · exact case2_13
  · exact case2_14
end PlaneResearch.CompactEightReject
