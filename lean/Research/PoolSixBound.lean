import Research.TablePool
import Research.PoolSixSAT

namespace PlaneResearch.PoolSixBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables PlaneResearch.TablePool
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def R : Finset (Table 8) := {0,1,2,4,8,16,32,64,255}
def U : Finset (Table 8) := {5,11,22,44,49,65,68,88,98}
def F : Finset (Table 8) := {11,22,44,49,88,98}

private lemma classify11 (a b : Table 8) (af : a ≠ 11) (bf : b ≠ 11) (op : recipe 11 a b) :
    (a ∈ [10,9,3,244] ∧ a ∉ R ∪ U) ∨ (b ∈ [10,9,3,244] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 11) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify22 (a b : Table 8) (af : a ≠ 22) (bf : b ≠ 22) (op : recipe 22 a b) :
    (a ∈ [20,18,6,233] ∧ a ∉ R ∪ U) ∨ (b ∈ [20,18,6,233] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 22) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify44 (a b : Table 8) (af : a ≠ 44) (bf : b ≠ 44) (op : recipe 44 a b) :
    (a ∈ [40,36,12,211] ∧ a ∉ R ∪ U) ∨ (b ∈ [40,36,12,211] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 44) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify49 (a b : Table 8) (af : a ≠ 49) (bf : b ≠ 49) (op : recipe 49 a b) :
    (a ∈ [48,33,17,206] ∧ a ∉ R ∪ U) ∨ (b ∈ [48,33,17,206] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 49) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify88 (a b : Table 8) (af : a ≠ 88) (bf : b ≠ 88) (op : recipe 88 a b) :
    (a ∈ [80,72,24,167] ∧ a ∉ R ∪ U) ∨ (b ∈ [80,72,24,167] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 88) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify98 (a b : Table 8) (af : a ≠ 98) (bf : b ≠ 98) (op : recipe 98 a b) :
    (a ∈ [96,66,34,157] ∧ a ∉ R ∪ U) ∨ (b ∈ [96,66,34,157] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 98) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

theorem lower (T : Finset (Table 8)) (sub : T ⊆ U) (must : F ⊆ T) (dis : Disjoint R T)
    (gs : List Gate) (w : List (Table 8)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : T.card+5+1 ≤ gs.length := by
  apply pool_lower R T (by decide) (by decide) dis _ gs w ok raw hit
  intro h order excluded realize
  let l := List.ofFn h
  have known (a : Table 8) : (a ∈ R ∪ T ∨ ∃ i, h i=a) → (a ∈ R ∪ U ∨ a ∈ l) := by
    rintro (base|made)
    · exact Or.inl (Finset.union_subset_union_right sub base)
    · exact Or.inr (List.mem_ofFn.mpr made)
  have row (f : Table 8) (hf : f ∈ F) : ∃ a b,
      (a ∈ R ∪ U ∨ a ∈ l) ∧ (b ∈ R ∪ U ∨ b ∈ l) ∧ a ≠ f ∧ b ≠ f ∧ recipe f a b := by
    obtain ⟨a,b,aa,bb,af,bf,op⟩ := realize f (must hf)
    exact ⟨a,b,known a aa,known b bb,af,bf,op⟩
  have safe (i : Fin 5) : PlaneResearch.PoolSixSAT.safe (h i) := by
    have notF : h i ∉ F := fun hf => excluded i (must hf)
    simpa only [F,Finset.mem_insert,Finset.mem_singleton,not_or,PlaneResearch.PoolSixSAT.safe] using notF
  apply PlaneResearch.PoolSixSAT.reject (h 0) (h 1) (h 2) (h 3) (h 4)
  · exact order 0 1 (by decide)
  · exact order 1 2 (by decide)
  · exact order 2 3 (by decide)
  · exact order 3 4 (by decide)
  · exact safe 0
  · exact safe 1
  · exact safe 2
  · exact safe 3
  · exact safe 4
  · exact admit_of (R ∪ U) l [10,9,3,244] 11 (row 11 (by decide)) classify11
  · exact admit_of (R ∪ U) l [20,18,6,233] 22 (row 22 (by decide)) classify22
  · exact admit_of (R ∪ U) l [40,36,12,211] 44 (row 44 (by decide)) classify44
  · exact admit_of (R ∪ U) l [48,33,17,206] 49 (row 49 (by decide)) classify49
  · exact admit_of (R ∪ U) l [80,72,24,167] 88 (row 88 (by decide)) classify88
  · exact admit_of (R ∪ U) l [96,66,34,157] 98 (row 98 (by decide)) classify98

end PlaneResearch.PoolSixBound
