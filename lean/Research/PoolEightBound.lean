import Research.TablePool
import Research.PoolEightSAT

namespace PlaneResearch.PoolEightBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables PlaneResearch.TablePool
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def R : Finset (Table 9) := {0,1,2,4,8,16,32,64,128,511}
def U : Finset (Table 9) := {22,25,44,69,98,138,161,208}
def F : Finset (Table 9) := {22,25,44,69,98,138,161,208}

private lemma classify22 (a b : Table 9) (af : a ≠ 22) (bf : b ≠ 22) (op : recipe 22 a b) :
    (a ∈ [20,18,6,489] ∧ a ∉ R ∪ U) ∨ (b ∈ [20,18,6,489] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 22) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify25 (a b : Table 9) (af : a ≠ 25) (bf : b ≠ 25) (op : recipe 25 a b) :
    (a ∈ [24,17,9,486] ∧ a ∉ R ∪ U) ∨ (b ∈ [24,17,9,486] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 25) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify44 (a b : Table 9) (af : a ≠ 44) (bf : b ≠ 44) (op : recipe 44 a b) :
    (a ∈ [40,36,12,467] ∧ a ∉ R ∪ U) ∨ (b ∈ [40,36,12,467] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 44) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify69 (a b : Table 9) (af : a ≠ 69) (bf : b ≠ 69) (op : recipe 69 a b) :
    (a ∈ [68,65,5,442] ∧ a ∉ R ∪ U) ∨ (b ∈ [68,65,5,442] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 69) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify98 (a b : Table 9) (af : a ≠ 98) (bf : b ≠ 98) (op : recipe 98 a b) :
    (a ∈ [96,66,34,413] ∧ a ∉ R ∪ U) ∨ (b ∈ [96,66,34,413] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 98) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify138 (a b : Table 9) (af : a ≠ 138) (bf : b ≠ 138) (op : recipe 138 a b) :
    (a ∈ [136,130,10,373] ∧ a ∉ R ∪ U) ∨ (b ∈ [136,130,10,373] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 138) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify161 (a b : Table 9) (af : a ≠ 161) (bf : b ≠ 161) (op : recipe 161 a b) :
    (a ∈ [160,129,33,350] ∧ a ∉ R ∪ U) ∨ (b ∈ [160,129,33,350] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 161) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

private lemma classify208 (a b : Table 9) (af : a ≠ 208) (bf : b ≠ 208) (op : recipe 208 a b) :
    (a ∈ [192,144,80,303] ∧ a ∉ R ∪ U) ∨ (b ∈ [192,144,80,303] ∧ b ∉ R ∪ U) ∨
    (a ∉ R ∪ U ∧ b ∉ R ∪ U ∧ a &&& b = 208) := by
  simp only [R,U,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,
    List.not_mem_nil,or_false,recipe] at *
  bv_decide

theorem lower (T : Finset (Table 9)) (sub : T ⊆ U) (must : F ⊆ T) (dis : Disjoint R T)
    (gs : List Gate) (w : List (Table 9)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : T.card+7+1 ≤ gs.length := by
  apply pool_lower R T (by decide) (by decide) dis _ gs w ok raw hit
  intro h order excluded realize
  let l := List.ofFn h
  have known (a : Table 9) : (a ∈ R ∪ T ∨ ∃ i, h i=a) → (a ∈ R ∪ U ∨ a ∈ l) := by
    rintro (base|made)
    · exact Or.inl (Finset.union_subset_union_right sub base)
    · exact Or.inr (List.mem_ofFn.mpr made)
  have row (f : Table 9) (hf : f ∈ F) : ∃ a b,
      (a ∈ R ∪ U ∨ a ∈ l) ∧ (b ∈ R ∪ U ∨ b ∈ l) ∧ a ≠ f ∧ b ≠ f ∧ recipe f a b := by
    obtain ⟨a,b,aa,bb,af,bf,op⟩ := realize f (must hf)
    exact ⟨a,b,known a aa,known b bb,af,bf,op⟩
  have safe (i : Fin 7) : PlaneResearch.PoolEightSAT.safe (h i) := by
    have notF : h i ∉ F := fun hf => excluded i (must hf)
    simpa only [F,Finset.mem_insert,Finset.mem_singleton,not_or,PlaneResearch.PoolEightSAT.safe] using notF
  apply PlaneResearch.PoolEightSAT.reject (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)
  · exact order 0 1 (by decide)
  · exact order 1 2 (by decide)
  · exact order 2 3 (by decide)
  · exact order 3 4 (by decide)
  · exact order 4 5 (by decide)
  · exact order 5 6 (by decide)
  · exact safe 0
  · exact safe 1
  · exact safe 2
  · exact safe 3
  · exact safe 4
  · exact safe 5
  · exact safe 6
  · exact admit_of (R ∪ U) l [20,18,6,489] 22 (row 22 (by decide)) classify22
  · exact admit_of (R ∪ U) l [24,17,9,486] 25 (row 25 (by decide)) classify25
  · exact admit_of (R ∪ U) l [40,36,12,467] 44 (row 44 (by decide)) classify44
  · exact admit_of (R ∪ U) l [68,65,5,442] 69 (row 69 (by decide)) classify69
  · exact admit_of (R ∪ U) l [96,66,34,413] 98 (row 98 (by decide)) classify98
  · exact admit_of (R ∪ U) l [136,130,10,373] 138 (row 138 (by decide)) classify138
  · exact admit_of (R ∪ U) l [160,129,33,350] 161 (row 161 (by decide)) classify161
  · exact admit_of (R ∪ U) l [192,144,80,303] 208 (row 208 (by decide)) classify208

end PlaneResearch.PoolEightBound
