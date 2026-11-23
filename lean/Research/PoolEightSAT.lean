import Research.SideTables

namespace PlaneResearch.PoolEightSAT
open PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def query (f : Table 9) (simple l : List (Table 9)) : Bool :=
  l.any (fun a => simple.contains a) || l.any (fun a => l.any (fun b => a &&& b == f))

def safe (a : Table 9) : Prop := a ≠ 22 ∧ a ≠ 25 ∧ a ≠ 44 ∧ a ≠ 69 ∧ a ≠ 98 ∧ a ≠ 138 ∧ a ≠ 161 ∧ a ≠ 208

theorem reject (a0 a1 a2 a3 a4 a5 a6 : Table 9)
    (o0 : a0 ≤ a1)
    (o1 : a1 ≤ a2)
    (o2 : a2 ≤ a3)
    (o3 : a3 ≤ a4)
    (o4 : a4 ≤ a5)
    (o5 : a5 ≤ a6)
    (s0 : safe a0)
    (s1 : safe a1)
    (s2 : safe a2)
    (s3 : safe a3)
    (s4 : safe a4)
    (s5 : safe a5)
    (s6 : safe a6)
    (h22 : query 22 [20,18,6,489] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h25 : query 25 [24,17,9,486] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h44 : query 44 [40,36,12,467] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h69 : query 69 [68,65,5,442] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h98 : query 98 [96,66,34,413] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h138 : query 138 [136,130,10,373] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h161 : query 161 [160,129,33,350] [a0,a1,a2,a3,a4,a5,a6] = true)
    (h208 : query 208 [192,144,80,303] [a0,a1,a2,a3,a4,a5,a6] = true) : False := by
  simp only [query,safe,List.any_cons,List.any_nil,List.contains_cons,List.contains_nil,Bool.or_false] at *
  bv_decide (config := { timeout := 600 })

end PlaneResearch.PoolEightSAT
