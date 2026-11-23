import Research.SideTables

namespace PlaneResearch.PoolSixSAT
open PlaneResearch.SideTables
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def query (f : Table 8) (simple l : List (Table 8)) : Bool :=
  l.any (fun a => simple.contains a) || l.any (fun a => l.any (fun b => a &&& b == f))

def safe (a : Table 8) : Prop := a ≠ 11 ∧ a ≠ 22 ∧ a ≠ 44 ∧ a ≠ 49 ∧ a ≠ 88 ∧ a ≠ 98

theorem reject (a0 a1 a2 a3 a4 : Table 8)
    (o0 : a0 ≤ a1)
    (o1 : a1 ≤ a2)
    (o2 : a2 ≤ a3)
    (o3 : a3 ≤ a4)
    (s0 : safe a0)
    (s1 : safe a1)
    (s2 : safe a2)
    (s3 : safe a3)
    (s4 : safe a4)
    (h11 : query 11 [10,9,3,244] [a0,a1,a2,a3,a4] = true)
    (h22 : query 22 [20,18,6,233] [a0,a1,a2,a3,a4] = true)
    (h44 : query 44 [40,36,12,211] [a0,a1,a2,a3,a4] = true)
    (h49 : query 49 [48,33,17,206] [a0,a1,a2,a3,a4] = true)
    (h88 : query 88 [80,72,24,167] [a0,a1,a2,a3,a4] = true)
    (h98 : query 98 [96,66,34,157] [a0,a1,a2,a3,a4] = true) : False := by
  simp only [query,safe,List.any_cons,List.any_nil,List.contains_cons,List.contains_nil,Bool.or_false] at *
  bv_decide (config := { timeout := 600 })

end PlaneResearch.PoolSixSAT
