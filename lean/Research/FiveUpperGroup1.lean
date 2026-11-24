import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup1
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0x80000000,4,[a 1 2,a 0 5,a 4 6,a 3 7]),
  (0x80808000,4,[o 3 4,a 2 5,a 1 6,a 0 7]),
  (0x88808000,6,[a 3 4,o 3 4,a 2 6,o 5 7,a 1 8,a 0 9]),
  (0x88808080,4,[a 3 4,o 2 5,a 1 6,a 0 7]),
  (0xa8808000,8,[o 3 4,a 1 2,o 1 2,a 4 7,a 3 8,o 6 9,a 5 10,a 0 11]),
  (0xa8808080,6,[a 1 2,o 1 2,a 4 6,a 3 7,o 5 8,a 0 9]),
  (0xe8808000,10,[a 0 1,o 0 1,a 4 6,o 5 7,a 3 8,a 2 9,o 2 9,a 7 11,a 5 12,o 10 13]),
  (0x88888880,4,[o 2 4,o 3 5,a 1 6,a 0 7]),
  (0xa8808880,6,[a 1 3,a 3 4,o 1 6,a 2 7,o 5 8,a 0 9]),
  (0xa888a000,4,[a 2 3,a 1 4,o 5 6,a 0 7]),
  (0xe8808080,8,[a 0 1,o 0 1,a 3 4,o 2 7,a 6 7,a 5 8,a 2 9,o 10 11]),
  (0xa8888880,7,[a 2 4,a 3 5,o 2 4,o 3 7,a 1 8,o 6 9,a 0 10]),
  (0xa888a080,5,[a 2 3,o 2 4,a 1 6,o 5 7,a 0 8]),
  (0xe8808880,8,[o 0 1,o 2 3,a 0 1,a 2 4,a 3 8,o 7 9,a 6 10,a 5 11]),
  (0xe888a000,6,[a 2 3,a 1 4,a 0 6,o 0 6,a 5 8,o 7 9]),
  (0xa8888888,4,[a 2 4,a 3 5,o 1 6,a 0 7]),
  (0xa888a880,6,[a 2 3,o 2 4,o 3 6,a 1 7,o 5 8,a 0 9]),
  (0xa8a8a800,4,[o 3 4,o 1 2,a 5 6,a 0 7]),
  (0xe880a880,8,[o 1 3,a 0 2,a 2 4,o 0 7,a 1 8,a 3 9,o 6 10,a 5 11]),
  (0xe8888880,9,[o 0 1,a 2 4,a 3 6,o 2 4,o 3 8,a 1 9,a 0 10,o 7 11,a 5 12]),
  (0xe888a080,7,[a 1 4,a 0 2,o 5 6,a 2 3,a 0 1,o 8 9,a 7 10]),
  (0xe888e000,6,[o 0 1,a 2 3,a 0 1,a 4 7,o 6 8,a 5 9]),
  (0xa8a8a880,6,[a 1 2,o 3 4,o 1 2,a 6 7,o 5 8,a 0 9]),
  (0xe8888888,6,[a 0 1,o 0 1,a 2 6,a 4 7,a 3 8,o 5 9]),
  (0xe888a880,8,[a 2 3,a 0 1,o 5 6,a 1 4,o 2 3,a 0 9,o 8 10,a 7 11]),
  (0xe888e080,7,[o 0 1,a 2 3,o 2 4,a 1 7,a 0 8,o 6 9,a 5 10]),
  (0xe8a8a800,8,[o 3 4,a 0 1,a 1 4,a 3 7,o 0 8,a 2 9,o 6 10,a 5 11]),
  (0xe8a8c800,6,[a 0 1,o 2 5,a 1 3,a 0 4,o 7 8,a 6 9]),
  (0xeaa8c000,7,[a 1 2,a 3 5,o 1 2,o 3 7,a 0 8,a 4 9,o 6 10]),
  (0xa8a8a888,4,[o 3 4,a 2 5,o 1 6,a 0 7])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup1
