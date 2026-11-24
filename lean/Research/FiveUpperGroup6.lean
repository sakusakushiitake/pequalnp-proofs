import Research.FiveUpperTables

namespace PlaneResearch.FiveUpperGroup6
open PlaneResearch.FiveUpperTables

def rows : List Row := [
  (0xfeeefac0,7,[a 0 3,o 1 3,a 2 6,o 0 1,a 4 8,o 7 9,o 5 10]),
  (0xeeeeeee8,6,[a 0 1,o 0 1,o 2 4,o 3 7,a 6 8,o 5 9]),
  (0xfeeaeaea,6,[a 1 2,o 1 2,a 4 6,a 3 7,o 5 8,o 0 9]),
  (0xfeeaeee8,8,[o 0 1,o 2 3,a 5 6,o 1 4,a 2 3,o 0 9,a 8 10,o 7 11]),
  (0xfeeafce8,7,[a 0 4,a 1 2,o 0 3,o 1 2,a 7 8,o 6 9,o 5 10]),
  (0xfeeeeee0,7,[a 2 4,a 3 5,o 0 1,o 2 4,o 3 8,a 7 9,o 6 10]),
  (0xfeeefaa8,8,[a 2 3,a 1 4,o 1 2,o 4 7,o 3 8,a 0 9,o 6 10,o 5 11]),
  (0xfeeefac8,6,[o 0 1,a 4 5,o 1 3,o 0 2,a 7 8,o 6 9]),
  (0xeeeeeeea,4,[o 2 4,o 3 5,a 1 6,o 0 7]),
  (0xfeeaeeea,6,[a 1 3,a 3 4,o 1 6,a 2 7,o 5 8,o 0 9]),
  (0xfeeafee8,8,[a 1 3,o 0 2,o 2 4,a 0 7,o 1 8,o 3 9,a 6 10,o 5 11]),
  (0xfeeeeee8,9,[a 0 1,a 2 4,a 3 6,o 0 1,o 2 4,o 3 9,a 8 10,o 7 11,o 5 12]),
  (0xfeeefaaa,4,[a 2 3,a 1 4,o 5 6,o 0 7]),
  (0xfeeefae8,7,[o 0 1,o 2 4,a 5 6,o 1 3,o 0 2,a 8 9,o 7 10]),
  (0xfeeefee0,6,[a 2 3,o 0 1,o 2 4,o 3 7,a 6 8,o 5 9]),
  (0xfeeeeeea,7,[a 2 4,a 3 5,o 2 4,o 3 7,a 1 8,o 6 9,o 0 10]),
  (0xfeeefaea,5,[a 2 3,o 2 4,a 1 6,o 5 7,o 0 8]),
  (0xfeeefee8,8,[a 2 3,a 0 1,o 0 1,o 2 4,o 3 8,a 7 9,o 6 10,o 5 11]),
  (0xfefefea8,6,[o 1 2,a 0 5,o 3 4,o 0 5,a 7 8,o 6 9]),
  (0xfeeeeeee,4,[a 2 4,a 3 5,o 1 6,o 0 7]),
  (0xfeeefeea,6,[a 2 3,o 2 4,o 3 6,a 1 7,o 5 8,o 0 9]),
  (0xfefefeaa,4,[o 3 4,o 1 2,a 5 6,o 0 7]),
  (0xfefefee8,8,[a 0 1,o 0 1,o 3 4,o 5 7,o 6 7,a 6 8,a 2 9,o 10 11]),
  (0xfefefeea,6,[a 1 2,o 3 4,o 1 2,a 6 7,o 5 8,o 0 9]),
  (0xfffefee8,10,[a 0 1,o 0 1,o 2 5,a 4 6,o 4 6,a 3 9,o 3 9,o 7 10,o 8 12,a 11 13]),
  (0xfefefeee,4,[o 3 4,a 2 5,o 1 6,o 0 7]),
  (0xfffefeea,8,[a 3 4,a 1 2,o 3 4,o 1 2,a 7 8,o 6 9,o 5 10,o 0 11]),
  (0xfffefeee,6,[a 3 4,o 3 4,a 2 6,o 5 7,o 1 8,o 0 9]),
  (0xfffefefe,4,[a 3 4,o 2 5,o 1 6,o 0 7]),
  (0xfffffffe,4,[o 1 2,o 0 5,o 4 6,o 3 7])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem verified : rows.all checked=true := by decide +kernel

end PlaneResearch.FiveUpperGroup6
