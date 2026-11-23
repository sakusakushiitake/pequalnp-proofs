import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem case1_5 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [61,155]=false := by decide +kernel
theorem case1_6 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [61,217]=false := by decide +kernel
theorem case1_7 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [61,219]=false := by decide +kernel
theorem case1_8 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [63,217]=false := by decide +kernel
theorem case1_9 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [93,155]=false := by decide +kernel
end PlaneResearch.CompactEightReject
