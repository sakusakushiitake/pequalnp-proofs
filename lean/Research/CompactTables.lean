import Research.TablePool

namespace PlaneResearch.CompactTables
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables PlaneResearch.TablePool

abbrev RowPlan (d : ℕ) := List (Table d × List (Finset ℕ))

def tags {d : ℕ} (base : Finset (Table d)) (code : Table d → ℕ) (a b : Table d) : Finset ℕ :=
  (({a,b} \ base).image code)

def checkRow {d : ℕ} (base : Finset (Table d)) (code : Table d → ℕ) (f : Table d)
    (alts : List (Finset ℕ)) : Bool :=
  (List.range (2^d)).all fun i =>
    let a := BitVec.ofNat d i
    (List.range (2^d)).all fun j =>
      let b := BitVec.ofNat d j
      if a ≠ f ∧ b ≠ f ∧ recipe f a b then alts.any (fun e => decide (e ⊆ tags base code a b)) else true

theorem checked {d : ℕ} (base : Finset (Table d)) (code : Table d → ℕ) (f : Table d)
    (alts : List (Finset ℕ)) (ok : checkRow base code f alts = true) (a b : Table d)
    (af : a ≠ f) (bf : b ≠ f) (rec : recipe f a b) :
    ∃ e ∈ alts, e ⊆ tags base code a b := by
  have aa := List.all_eq_true.mp ok a.toNat (List.mem_range.mpr a.isLt)
  have bb := List.all_eq_true.mp aa b.toNat (List.mem_range.mpr b.isLt)
  have ea : BitVec.ofNat d a.toNat = a := by simp
  have eb : BitVec.ofNat d b.toNat = b := by simp
  simp only [ea,eb] at bb
  rw [if_pos ⟨af,bf,rec⟩] at bb
  obtain ⟨e,he,sub⟩ := List.any_eq_true.mp bb
  exact ⟨e,he,of_decide_eq_true sub⟩

/-- Identifying intermediate signatures can only decrease their cardinality.
Every supplied local option must remain necessary after taking this image. -/
theorem lower {d k : ℕ} (R T U : Finset (Table d)) (code : Table d → ℕ) (plan : RowPlan d)
    (rz : 0 ∈ R) (rt : top d ∈ R) (dis : Disjoint R T) (sub : T ⊆ U)
    (targets : ∀ v ∈ plan, v.1 ∈ T)
    (check : ∀ v ∈ plan, checkRow (R ∪ U) code v.1 v.2 = true)
    (reject : possible k ∅ (plan.map Prod.snd) = false)
    (gs : List Gate) (w : List (Table d)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : T.card+k+1 ≤ gs.length := by
  classical
  apply pool_lower R T rz rt dis _ gs w ok raw hit
  intro h _ _ realize
  let P := Finset.univ.image (fun j => code (h j))
  have num : P.card ≤ k := by simpa [P] using Finset.card_image_le (s := Finset.univ) (f := fun j => code (h j))
  have works (row) (hr : row ∈ plan.map Prod.snd) : ∃ e ∈ row, e ⊆ P := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    obtain ⟨a,b,aa,bb,af,bf,rec⟩ := realize v.1 (targets v hv)
    obtain ⟨e,he,need⟩ := checked (R ∪ U) code v.1 v.2 (check v hv) a b af bf rec
    refine ⟨e,he,fun y hy => ?_⟩
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (need hy)
    obtain ⟨pair,out⟩ := Finset.mem_sdiff.mp hx
    have way : x ∈ R ∪ T ∨ ∃ i, h i=x := by
      rcases Finset.mem_insert.mp pair with rfl|hb
      · exact aa
      · have eq := Finset.mem_singleton.mp hb
        exact eq ▸ bb
    obtain ⟨i,eq⟩ := way.resolve_left (fun h => out (Finset.union_subset_union_right sub h))
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg code eq⟩
  have accept := possible_of k P num _ works ∅ (Finset.empty_subset _)
  simp [reject] at accept

end PlaneResearch.CompactTables
