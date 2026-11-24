import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup2
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0xaaa8a880,8,[a 3 4,a 1 2,o 3 4,o 1 2,a 7 8,o 6 9,o 5 10,a 0 11]),
  (0xe888a888,6,[a 0 1,a 1 4,o 0 6,a 2 7,a 3 8,o 5 9]),
  (0xe888e880,8,[o 0 1,a 2 3,o 2 4,o 3 7,a 1 8,a 0 9,o 6 10,a 5 11]),
  (0xe8a8a880,9,[o 1 2,a 3 4,o 0 6,a 1 2,o 3 4,a 0 9,o 8 10,a 7 11,a 5 12]),
  (0xe8a8c880,8,[a 0 1,o 2 5,a 1 3,a 1 2,o 4 8,a 0 9,o 7 10,a 6 11]),
  (0xe8a8e800,7,[o 3 4,a 0 1,a 1 3,o 0 7,a 2 8,o 6 9,a 5 10]),
  (0xeaa8c080,7,[o 1 2,a 0 5,o 3 6,a 0 4,a 1 2,o 8 9,a 7 10]),
  (0xeaaac000,4,[a 0 4,a 1 2,a 3 6,o 5 7]),
  (0xeac8e000,7,[o 3 4,a 0 3,o 1 6,a 0 4,o 2 8,a 7 9,a 5 10]),
  (0xaaa8a888,6,[a 3 4,o 3 4,a 2 6,o 5 7,o 1 8,a 0 9]),
  (0xe8a8a888,8,[a 0 1,o 3 4,a 1 4,a 3 7,o 0 8,a 6 9,a 2 10,o 5 11]),
  (0xe8a8c888,6,[a 0 1,a 1 3,a 0 4,o 6 7,a 2 8,o 5 9]),
  (0xe8a8e880,8,[o 0 3,a 1 2,o 3 4,o 1 2,a 7 8,a 0 9,o 6 10,a 5 11]),
  (0xe8e8e800,6,[o 3 4,a 0 1,o 0 1,a 2 7,o 6 8,a 5 9]),
  (0xeaa8a880,9,[a 3 4,o 1 2,a 0 6,o 5 7,a 1 2,o 3 4,a 0 10,o 9 11,a 8 12]),
  (0xeaa8c880,9,[o 0 3,a 0 4,o 1 6,a 1 4,o 3 8,a 0 9,o 2 10,a 7 11,a 5 12]),
  (0xeaaac080,5,[a 0 4,o 0 3,a 2 6,a 1 7,o 5 8]),
  (0xeac0e880,8,[a 0 3,a 1 2,o 5 6,a 2 3,a 0 1,o 8 9,o 4 10,a 7 11]),
  (0xeac8e080,8,[o 1 3,a 0 4,o 3 4,a 1 7,o 0 8,a 2 9,o 6 10,a 5 11]),
  (0xaaa8a8a8,4,[a 3 4,o 2 5,o 1 6,a 0 7]),
  (0xe8a8a8a8,6,[a 0 1,a 1 4,a 3 6,o 0 7,a 2 8,o 5 9]),
  (0xe8a8e888,7,[a 0 1,o 3 4,a 1 3,o 0 7,a 6 8,a 2 9,o 5 10]),
  (0xe8e8e880,8,[a 0 1,o 0 1,o 3 4,a 6 7,a 2 8,o 2 8,a 5 10,o 9 11]),
  (0xeaa8a888,9,[a 1 3,o 0 5,a 2 4,o 2 4,a 3 8,o 1 9,a 0 10,o 7 11,a 6 12]),
  (0xeaa8c888,7,[a 1 2,a 3 5,o 2 3,a 4 7,o 1 8,a 0 9,o 6 10]),
  (0xeaa8e880,9,[o 1 2,a 1 2,a 0 5,a 3 5,o 3 7,o 4 8,a 0 10,o 6 11,a 9 12]),
  (0xeaaac880,7,[a 0 4,a 0 3,o 0 3,a 2 7,o 6 8,a 1 9,o 5 10]),
  (0xeac0e8c0,6,[a 1 2,o 1 2,o 4 6,a 0 7,a 3 8,o 5 9]),
  (0xeac8e0c0,5,[a 0 3,o 1 5,a 0 4,o 2 7,a 6 8]),
  (0xeac8e880,9,[o 1 3,a 0 2,a 1 3,o 4 7,a 1 2,o 0 9,a 8 10,o 6 11,a 5 12])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup2
