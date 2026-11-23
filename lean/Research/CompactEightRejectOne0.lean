import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem case1_0 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [230]=false := by decide +kernel
theorem case1_1 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [257]=false := by decide +kernel
theorem case1_2 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [31,185]=false := by decide +kernel
theorem case1_3 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [31,217]=false := by decide +kernel
theorem case1_4 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [31,249]=false := by decide +kernel
end PlaneResearch.CompactEightReject
