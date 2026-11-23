import Research.CompactEightChoices

namespace PlaneResearch.CompactEightReject
open PlaneResearch.CompactBits PlaneResearch.CompactEight PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
theorem case1_10 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [93,185]=false := by decide +kernel
theorem case1_11 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [93,187]=false := by decide +kernel
theorem case1_12 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [95,185]=false := by decide +kernel
theorem case1_13 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [123,157]=false := by decide +kernel
theorem case1_14 : branch 115792089237316195423570985008687907853269984665640564039457584007913129639936 6 tailRows [125,155]=false := by decide +kernel
end PlaneResearch.CompactEightReject
