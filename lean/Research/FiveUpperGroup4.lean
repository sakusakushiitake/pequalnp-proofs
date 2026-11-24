import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup4
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0xeaeaea80,6,[a 1 2,a 0 5,o 3 4,o 0 5,a 7 8,o 6 9]),
  (0xeee0e8e0,6,[o 0 1,a 0 1,o 4 6,a 3 7,o 2 8,a 5 9]),
  (0xeee0eac0,7,[a 0 3,a 0 4,o 1 6,a 3 4,o 2 8,a 7 9,o 5 10]),
  (0xeee8e888,8,[a 0 1,o 3 4,o 0 1,a 3 4,o 2 8,a 7 9,a 6 10,o 5 11]),
  (0xeee8e8a0,8,[a 3 4,o 3 4,a 1 6,a 0 7,o 0 7,o 2 8,o 5 10,a 9 11]),
  (0xfee8e880,10,[a 0 1,o 0 1,a 2 4,o 2 4,o 5 7,a 6 8,a 9 10,o 9 10,o 3 11,a 12 13]),
  (0xeaaaaaaa,4,[a 1 2,a 4 5,a 3 6,o 0 7]),
  (0xeaaaeaa8,7,[a 1 2,a 3 5,o 1 2,o 4 7,o 3 8,a 0 9,o 6 10]),
  (0xeae8e8e8,6,[a 1 2,a 3 4,o 2 6,o 1 7,a 0 8,o 5 9]),
  (0xeae8eaa8,7,[o 1 3,a 0 5,o 3 4,a 1 7,o 0 8,a 2 9,o 6 10]),
  (0xeae8eac8,6,[a 1 2,a 2 4,o 1 6,o 3 7,a 0 8,o 5 9]),
  (0xeaeaea88,6,[a 0 1,o 3 4,a 1 2,o 0 7,a 6 8,o 5 9]),
  (0xeaeaeac0,4,[a 1 2,o 3 4,a 0 6,o 5 7]),
  (0xeee0eae0,5,[o 0 1,o 0 4,a 3 6,o 2 7,a 5 8]),
  (0xeee8e8a8,8,[a 0 1,a 3 4,o 2 6,o 3 4,a 1 8,o 0 9,a 7 10,o 5 11]),
  (0xeee8e8e0,8,[o 0 1,a 3 4,o 3 4,a 1 7,a 0 8,o 6 9,o 2 10,a 5 11]),
  (0xeee8eaa0,8,[a 2 3,o 4 5,a 1 6,a 0 7,o 0 7,o 3 8,o 2 10,a 9 11]),
  (0xeee8eac0,8,[a 3 4,o 2 5,a 1 6,o 1 2,a 4 8,o 3 9,a 0 10,o 7 11]),
  (0xfee8e888,10,[a 0 1,o 0 1,a 2 3,o 2 3,o 4 6,a 6 8,a 4 10,o 7 11,a 9 12,o 5 13]),
  (0xeaeaeaa8,7,[o 1 2,a 0 5,o 3 4,a 1 2,o 0 8,a 7 9,o 6 10]),
  (0xeaeaeac8,5,[a 1 2,o 1 4,o 3 6,a 0 7,o 5 8]),
  (0xeee8e8e8,6,[a 0 1,o 0 1,a 3 4,o 2 7,a 6 8,o 5 9]),
  (0xeee8eaa8,8,[a 0 1,o 2 3,a 2 3,o 4 7,a 1 8,o 0 9,a 6 10,o 5 11]),
  (0xeee8eac8,8,[o 0 1,o 2 3,a 4 6,o 1 3,o 0 2,a 8 9,o 7 10,a 5 11]),
  (0xeee8eae0,7,[o 2 3,a 0 5,o 0 3,a 4 7,o 2 8,a 1 9,o 6 10]),
  (0xeeeaeaa0,8,[a 0 3,o 2 4,a 2 4,o 3 7,a 1 8,o 0 9,a 6 10,o 5 11]),
  (0xeeeaeac0,6,[o 3 4,a 0 5,a 3 4,o 2 7,a 1 8,o 6 9]),
  (0xfee8e8a8,10,[a 1 2,o 1 2,a 3 5,o 3 5,a 4 8,a 0 9,o 0 9,a 6 11,o 10 12,o 7 13]),
  (0xfee8eac0,8,[a 0 3,a 1 2,o 0 3,o 1 2,a 7 8,a 4 9,o 6 10,o 5 11]),
  (0xeaeaeaaa,4,[o 3 4,a 2 5,a 1 6,o 0 7])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup4
