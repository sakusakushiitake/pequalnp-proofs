import Research.StarCounting

namespace PlaneResearch.PriorityFamilies

variable {V : Type*} [DecidableEq V]

/-- Keep the vertices in R whenever any are present. -/
def prefer (R S : Finset V) : Finset V :=
  if Disjoint S R then S else S ∩ R

theorem subset (R S : Finset V) : prefer R S ⊆ S := by
  unfold prefer
  split
  · exact Finset.Subset.rfl
  · exact Finset.inter_subset_left

theorem mem_prefer {R S : Finset V} {v : V} (h : v ∈ S)
    (keep : v ∈ R ∨ Disjoint S R) : v ∈ prefer R S := by
  by_cases d : Disjoint S R
  · simpa [prefer,d] using h
  · exact (by simp [prefer,d,h,keep.resolve_right d])

theorem union_cases (R A B : Finset V) :
    prefer R (A ∪ B)=prefer R A ∨ prefer R (A ∪ B)=prefer R B ∨
      prefer R (A ∪ B)=prefer R A ∪ prefer R B := by
  by_cases a : Disjoint A R <;> by_cases b : Disjoint B R
  · exact Or.inr (Or.inr (by simp [prefer,Finset.disjoint_union_left,a,b]))
  · right; left
    have emp : A ∩ R = ∅ := Finset.disjoint_iff_inter_eq_empty.mp a
    simp [prefer,Finset.disjoint_union_left,a,b,Finset.union_inter_distrib_right,emp]
  · left
    have emp : B ∩ R = ∅ := Finset.disjoint_iff_inter_eq_empty.mp b
    simp [prefer,Finset.disjoint_union_left,a,b,Finset.union_inter_distrib_right,emp]
  · exact Or.inr (Or.inr (by simp [prefer,Finset.disjoint_union_left,a,b,Finset.union_inter_distrib_right]))

theorem projected_split (R : Finset V) (F : Finset (Finset V))
    (split : ∀ s ∈ F, 1<s.card → ∃ a ∈ F, ∃ b ∈ F, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s)
    (z : Finset V) (hz : z ∈ F.image (prefer R)) (big : 1<z.card) :
    ∃ a ∈ F.image (prefer R), ∃ b ∈ F.image (prefer R),
      a.card<z.card ∧ b.card<z.card ∧ a ∪ b=z := by
  classical
  obtain ⟨s,sf,eq⟩ := Finset.mem_image.mp hz
  let D := F.filter (fun t => prefer R t=z)
  obtain ⟨t,ht,minimal⟩ := Finset.exists_min_image D Finset.card
    (show D.Nonempty from ⟨s,Finset.mem_filter.mpr ⟨sf,eq⟩⟩)
  obtain ⟨tf,tz⟩ := Finset.mem_filter.mp ht
  have sz := Finset.card_le_card (subset R t)
  rw [tz] at sz
  obtain ⟨a,af,b,bf,la,lb,ab⟩ := split t tf (by omega)
  have ne (u : Finset V) (uf : u ∈ F) (lt : u.card<t.card) : prefer R u ≠ z :=
    fun h => (Nat.not_le_of_gt lt) (minimal u (Finset.mem_filter.mpr ⟨uf,h⟩))
  have alt := union_cases R a b
  rw [ab,tz] at alt
  rcases alt with xa|xb|both
  · exact (ne a af la xa.symm).elim
  · exact (ne b bf lb xb.symm).elim
  · have incA : prefer R a ⊆ z := both ▸ Finset.subset_union_left
    have incB : prefer R b ⊆ z := both ▸ Finset.subset_union_right
    exact ⟨_,Finset.mem_image_of_mem _ af,_,Finset.mem_image_of_mem _ bf,
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨incA,ne a af la⟩),
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨incB,ne b bf lb⟩),both.symm⟩

theorem big_count (R : Finset V) (F : Finset (Finset V)) :
    ((F.image (prefer R)).filter (fun s => 1<s.card)).card ≤ (F.filter (fun s => 1<s.card)).card := by
  classical
  refine le_trans (Finset.card_le_card (t := (F.filter (fun s => 1<s.card)).image (prefer R)) ?_) Finset.card_image_le
  intro z hz
  obtain ⟨mem,big⟩ := Finset.mem_filter.mp hz
  obtain ⟨s,sf,rfl⟩ := Finset.mem_image.mp mem
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨sf,lt_of_lt_of_le big (Finset.card_le_card (subset R s))⟩)

end PlaneResearch.PriorityFamilies
