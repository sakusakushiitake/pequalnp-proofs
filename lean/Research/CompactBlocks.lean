import Research.CompactTables

namespace PlaneResearch.CompactBlocks
open PlaneResearch.SideTables PlaneResearch.CompactTables

def checkBlock {d : ℕ} (B : Finset (Table d)) (code : Table d → ℕ) (f : Table d)
    (alts : List (Finset ℕ)) (offset width : ℕ) : Bool :=
  (List.range width).all fun i =>
    let a := BitVec.ofNat d (offset+i)
    (List.range (2^d)).all fun j =>
      let b := BitVec.ofNat d j
      if a ≠ f ∧ b ≠ f ∧ recipe f a b then alts.any (fun e => decide (e ⊆ tags B code a b)) else true

theorem combine {d : ℕ} (B : Finset (Table d)) (code : Table d → ℕ) (f : Table d)
    (alts : List (Finset ℕ)) (width blocks : ℕ) (pos : 0<width) (size : 2^d=width*blocks)
    (checks : ∀ j : Fin blocks, checkBlock B code f alts (width*j.val) width=true) :
    checkRow B code f alts=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have bound : i/width<blocks := (Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm,size] using List.mem_range.mp hi)
  have part := List.all_eq_true.mp (checks ⟨i/width,bound⟩) (i%width) (List.mem_range.mpr (Nat.mod_lt _ pos))
  simpa only [Nat.div_add_mod] using part

end PlaneResearch.CompactBlocks
