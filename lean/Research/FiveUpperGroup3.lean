import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup3
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0xeae8e800,8,[o 3 4,a 1 2,a 3 4,o 2 7,o 1 8,a 0 9,o 6 10,a 5 11]),
  (0xe8e8e888,6,[a 0 1,o 3 4,o 0 1,a 6 7,a 2 8,o 5 9]),
  (0xeaa8a8a8,7,[o 1 2,a 0 5,a 1 2,o 0 7,a 4 8,a 3 9,o 6 10]),
  (0xeaa8e888,8,[o 0 1,a 2 3,o 2 3,a 4 7,o 1 8,a 0 9,o 6 10,a 5 11]),
  (0xeaaac888,5,[a 0 4,a 2 3,o 0 6,a 1 7,o 5 8]),
  (0xeaaae880,8,[o 0 3,a 1 2,o 1 2,a 3 7,o 4 8,a 0 9,o 6 10,a 5 11]),
  (0xeac8e888,8,[a 0 1,a 2 3,o 4 6,a 0 3,a 1 2,o 8 9,a 7 10,o 5 11]),
  (0xeac8e8c0,7,[a 0 3,o 1 5,a 1 3,o 4 7,a 0 8,o 2 9,a 6 10]),
  (0xeae8e880,10,[a 1 2,o 1 2,a 4 6,o 4 6,a 0 8,a 5 9,o 5 9,o 3 10,o 7 12,a 11 13]),
  (0xeae8ea00,6,[a 1 2,o 0 5,o 1 2,a 4 7,o 3 8,a 6 9]),
  (0xeee0e880,8,[o 0 1,a 2 3,o 2 3,a 0 1,o 4 8,a 7 9,o 6 10,a 5 11]),
  (0xaaaaaaa8,4,[o 1 2,o 4 5,o 3 6,a 0 7]),
  (0xe8e8e8a8,6,[a 0 1,o 3 4,a 1 6,o 0 7,a 2 8,o 5 9]),
  (0xeaa8aaa8,7,[o 1 3,a 0 5,a 1 4,a 3 7,o 0 8,a 2 9,o 6 10]),
  (0xeaa8e8a8,7,[a 1 2,a 3 5,a 3 4,o 2 7,o 1 8,a 0 9,o 6 10]),
  (0xeaaae888,6,[o 0 1,a 2 3,o 1 4,a 0 7,o 6 8,a 5 9]),
  (0xeac8e8c8,6,[a 1 2,o 2 4,a 3 6,o 1 7,a 0 8,o 5 9]),
  (0xeac8eac0,5,[a 0 3,a 0 4,o 2 6,a 1 7,o 5 8]),
  (0xeae8e888,8,[o 0 1,o 3 4,a 2 6,a 3 4,o 1 8,a 0 9,o 7 10,a 5 11]),
  (0xeae8e8c0,8,[a 1 2,a 3 4,o 3 4,o 1 2,a 7 8,o 6 9,a 0 10,o 5 11]),
  (0xeae8ea80,8,[a 1 2,o 1 2,a 0 5,o 0 5,a 4 6,o 3 9,o 7 10,a 8 11]),
  (0xeaeaea00,4,[o 3 4,a 1 2,o 0 6,a 5 7]),
  (0xeee0e8a0,8,[o 1 4,a 3 5,o 2 6,a 2 3,o 4 8,a 1 9,o 0 10,a 7 11]),
  (0xeee8e880,10,[a 2 3,o 2 3,o 4 5,a 0 7,o 0 7,a 6 9,a 1 10,o 1 10,a 8 12,o 11 13]),
  (0xeaaaaaa8,8,[a 1 2,a 4 5,a 3 6,o 1 2,o 4 8,o 3 9,a 0 10,o 7 11]),
  (0xeaaae8a8,6,[a 1 2,a 3 5,o 1 2,o 4 7,a 0 8,o 6 9]),
  (0xeae8e8a8,8,[o 3 4,a 2 5,a 1 6,a 3 4,o 2 8,o 1 9,a 0 10,o 7 11]),
  (0xeae8e8c8,8,[a 1 2,a 3 4,o 3 4,a 2 7,o 6 8,o 1 9,a 0 10,o 5 11]),
  (0xeae8ea88,7,[a 0 1,a 1 2,o 0 6,a 2 4,o 3 8,a 7 9,o 5 10]),
  (0xeae8eac0,6,[a 1 2,o 1 2,a 4 6,o 3 7,a 0 8,o 5 9])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup3
