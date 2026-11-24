import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup5
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0xeaeaeae8,6,[a 1 2,o 1 2,o 4 6,o 3 7,a 0 8,o 5 9]),
  (0xeee8eae8,7,[a 0 1,o 0 1,o 0 4,a 3 7,o 2 8,a 6 9,o 5 10]),
  (0xeee8eee0,6,[o 0 1,a 0 1,a 4 6,o 2 7,o 3 8,a 5 9]),
  (0xeeeaeaa8,9,[o 1 3,a 0 5,o 2 4,a 2 4,o 3 8,a 1 9,o 0 10,a 7 11,o 6 12]),
  (0xeeeaeac8,7,[o 3 4,a 0 5,a 3 4,o 2 7,o 0 8,a 1 9,o 6 10]),
  (0xeeeaeae0,7,[a 0 3,o 0 1,o 0 3,a 4 7,o 2 8,a 6 9,o 5 10]),
  (0xeeeaece0,5,[o 2 4,a 0 5,o 2 3,a 1 7,o 6 8]),
  (0xfee8e8e8,8,[a 3 4,a 2 5,o 2 5,o 1 6,a 7 8,o 7 8,a 0 10,o 9 11]),
  (0xfee8eaa8,9,[a 1 2,o 1 2,o 0 5,o 3 5,a 3 7,a 4 8,o 0 10,a 6 11,o 9 12]),
  (0xfee8eac8,9,[a 0 3,a 1 2,a 3 4,o 0 7,a 2 4,o 1 9,a 8 10,o 6 11,o 5 12]),
  (0xfeeaeac0,8,[a 0 3,a 1 2,o 1 2,a 3 7,o 0 8,a 4 9,o 6 10,o 5 11]),
  (0xeeeaeaaa,6,[a 3 4,o 3 4,a 2 6,o 5 7,a 1 8,o 0 9]),
  (0xeeeaeae8,8,[o 0 1,a 3 4,o 1 4,o 3 7,a 0 8,o 6 9,o 2 10,a 5 11]),
  (0xeeeaece8,6,[o 0 1,o 0 3,o 1 4,a 6 7,o 2 8,a 5 9]),
  (0xeeeaeee0,5,[a 0 4,o 0 1,o 2 3,a 6 7,o 5 8]),
  (0xfee8eae8,8,[a 0 3,a 1 2,o 1 2,a 3 4,o 0 8,a 7 9,o 6 10,o 5 11]),
  (0xfee8eee0,8,[o 0 1,o 2 3,a 5 6,a 2 3,a 0 1,o 8 9,a 4 10,o 7 11]),
  (0xfeeaeaa8,9,[o 1 2,a 3 4,o 0 6,a 5 7,o 3 4,a 1 2,o 0 10,a 9 11,o 8 12]),
  (0xfeeaeac8,9,[a 0 3,o 0 2,a 1 6,o 1 2,a 3 8,o 0 9,a 4 10,o 7 11,o 5 12]),
  (0xfeeaece0,8,[a 1 3,a 0 4,a 3 4,o 1 7,o 0 8,a 2 9,o 6 10,o 5 11]),
  (0xfeeafcc0,6,[a 1 3,a 0 4,o 1 3,a 2 7,o 6 8,o 5 9]),
  (0xeeeaeaea,4,[a 3 4,o 2 5,a 1 6,o 0 7]),
  (0xeeeaeee8,6,[o 0 1,o 1 4,a 0 6,o 2 7,o 3 8,a 5 9]),
  (0xeeeeeee0,4,[o 0 1,o 2 4,o 3 6,a 5 7]),
  (0xfee8eee8,8,[a 0 1,o 2 3,a 2 4,a 3 7,o 1 8,o 0 9,a 6 10,o 5 11]),
  (0xfeeaeaaa,8,[o 3 4,a 1 2,o 1 2,a 4 7,a 3 8,o 6 9,a 5 10,o 0 11]),
  (0xfeeaeae8,9,[a 1 2,a 3 4,o 0 6,o 3 4,a 0 8,o 2 9,o 1 10,a 7 11,o 5 12]),
  (0xfeeaece8,8,[o 0 1,a 2 5,o 0 3,o 0 2,a 4 8,o 1 9,a 7 10,o 6 11]),
  (0xfeeaeee0,7,[a 2 3,o 0 5,a 4 6,o 0 1,o 2 3,a 8 9,o 7 10]),
  (0xfeeafcc8,7,[a 1 3,o 1 4,a 0 6,o 1 3,a 2 8,o 7 9,o 5 10])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup5
