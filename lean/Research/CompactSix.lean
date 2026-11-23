import Research.CompactTables

namespace PlaneResearch.CompactSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables PlaneResearch.CompactTables
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

def R : Finset (Table 8) := {0,1,2,4,8,16,32,64,255}
def U : Finset (Table 8) := {5,11,22,44,49,65,68,88,98}
def F : Finset (Table 8) := {11,22,44,49,88,98}
private def packed : ℕ := 0x7f7e7d7c7b7a798477768380738583706f6e82826b85816885856564858561855f5e84845b848484818155548252518480834d4c804a498447464544438541403f3e3d823b3a833837818334833283832f828282802a298284262582238583201f81851c801a19848181158113818310800e0d82808080080781050480020100
private def code (v : Table 8) : ℕ := (packed >>> (8*(v.toNat % 128))) % 256
private def options11 : List (Finset ℕ) := [{128},{31,107},{47,91}]
private def options22 : List (Finset ℕ) := [{129},{31,118},{55,94}]
private def options44 : List (Finset ℕ) := [{130},{47,124},{61,110}]
private def options49 : List (Finset ℕ) := [{131},{55,121},{61,115}]
private def options88 : List (Finset ℕ) := [{132},{91,124},{94,121}]
private def options98 : List (Finset ℕ) := [{133},{107,118},{110,115}]
private theorem check11 : checkRow (R ∪ U) code 11 options11 = true := by decide +kernel
private theorem check22 : checkRow (R ∪ U) code 22 options22 = true := by decide +kernel
private theorem check44 : checkRow (R ∪ U) code 44 options44 = true := by decide +kernel
private theorem check49 : checkRow (R ∪ U) code 49 options49 = true := by decide +kernel
private theorem check88 : checkRow (R ∪ U) code 88 options88 = true := by decide +kernel
private theorem check98 : checkRow (R ∪ U) code 98 options98 = true := by decide +kernel
private def choices : RowPlan 8 := [(11,options11),(22,options22),(44,options44),(49,options49),(88,options88),(98,options98)]
private lemma reject : possible 5 ∅ (choices.map Prod.snd) = false := by decide +kernel

theorem lower (T : Finset (Table 8)) (sub : T ⊆ U) (must : F ⊆ T) (dis : Disjoint R T)
    (gs : List Gate) (w : List (Table 8)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) : T.card+5+1 ≤ gs.length := by
  apply PlaneResearch.CompactTables.lower R T U code choices (by decide) (by decide) dis sub _ _ reject gs w ok raw hit
  · intro v hv
    apply must
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro v hv
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    · exact check11
    · exact check22
    · exact check44
    · exact check49
    · exact check88
    · exact check98

end PlaneResearch.CompactSix
