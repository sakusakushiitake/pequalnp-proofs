import Research.TableGateSearch
import Research.ShardFourEssential
import PEqualNP.MetaComplexity.Helpers.ForestElim

namespace PlaneResearch.ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.Forest
open PlaneResearch.TableGateSearch

private def pool : List (BitVec 8) := [0,255,170,204,240]
private def code (x : ℕ) (i : Fin 5) := x.testBit i.val
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private theorem majority : can (232 : BitVec 8) 3 pool=false := by decide +kernel

theorem six_1 : ¬HasCircuitSize 5 (function 1) 5 := by
  intro h
  let f := function 1
  let g := fun x => f (Function.update x (3 : Fin 5) true)
  let h' := fun x => g (Function.update x (4 : Fin 5) true)
  have s1 : HasCircuitSize 5 g 4 :=
    one_gate_at 4 f 3 true 4 ⟨code 5,by decide +kernel⟩
      ⟨code 0,code 3,by decide +kernel⟩ h
  have s2 : HasCircuitSize 5 h' 3 :=
    one_gate_at 4 g 4 true 3 ⟨code 6,by decide +kernel⟩
      ⟨code 0,code 3,by decide +kernel⟩ s1
  let w : List (BitVec 8) := [170,204,240,0,0]
  let x := fun (j : Fin 8) (i : Fin 5) => (w.getD i.val 0).getLsbD j.val
  exact sampled_lower h' 232 w pool x (by decide +kernel) (by decide +kernel)
    (by simp [w,pool]) (by decide +kernel) (by decide +kernel) (by decide +kernel) majority s2

theorem exclude_1 (gs : List Gate) (o : ℕ) (ok : Allowed gs)
    (computes : Computes (table 1) gs o) : Replacement (table 1) gs := by
  apply large_has_replacement
  change 6≤gs.length
  by_contra! short
  exact six_1 ⟨⟨gs,o⟩,fun g hg => ok g hg,by change gs.length≤5; omega,computes⟩

theorem six_9 : ¬HasCircuitSize 5 (function 9) 5 := by
  intro h
  let f := function 9
  let g := fun x => f (Function.update x (0 : Fin 5) true)
  let h' := fun x => g (Function.update x (1 : Fin 5) false)
  have s1 : HasCircuitSize 5 g 4 :=
    one_gate_at 4 f 0 true 4 ⟨code 2,by decide +kernel⟩
      ⟨code 0,code 2,by decide +kernel⟩ h
  have s2 : HasCircuitSize 5 h' 3 :=
    one_gate_at 4 g 1 false 3 ⟨code 0,by decide +kernel⟩
      ⟨code 0,code 12,by decide +kernel⟩ s1
  let w : List (BitVec 8) := [0,0,170,204,240]
  let x := fun (j : Fin 8) (i : Fin 5) => (w.getD i.val 0).getLsbD j.val
  exact sampled_lower h' 232 w pool x (by decide +kernel) (by decide +kernel)
    (by simp [w,pool]) (by decide +kernel) (by decide +kernel) (by decide +kernel) majority s2

theorem exclude_9 (gs : List Gate) (o : ℕ) (ok : Allowed gs)
    (computes : Computes (table 9) gs o) : Replacement (table 9) gs := by
  apply large_has_replacement
  change 6≤gs.length
  by_contra! short
  exact six_9 ⟨⟨gs,o⟩,fun g hg => ok g hg,by change gs.length≤5; omega,computes⟩

end PlaneResearch.ShardFour
