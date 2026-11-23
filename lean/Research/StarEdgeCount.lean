import Research.StarCounting

namespace PlaneResearch.StarCounting
open PlaneResearch.BicliqueStar

/-- A star cover of the edge set can use multiple roots for one center.
Each distinct nonsingleton union used by a center is counted once, and
square-freeness prevents two different centers from charging the same union. -/
theorem star_edges {V I : Type*} [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (sq : NoSquare G) (E : Finset (Sym2 V))
    (T : Finset I) (center : I → V) (leaves : I → Finset V) (U : Finset (Finset V))
    (root : ∀ t ∈ T, leaves t ∈ U) (adj : ∀ t ∈ T, ∀ p ∈ leaves t, G.Adj (center t) p)
    (edges : ∀ e ∈ E, ∃ t ∈ T, ∃ p ∈ leaves t, e=s(center t,p))
    (split : ∀ s ∈ U, 1<s.card → ∃ a ∈ U, ∃ b ∈ U, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    E.card ≤ T.card + (U.filter (fun s => 1<s.card)).card := by
  classical
  let K := T.image center
  let J (c : V) := T.filter (fun t => center t=c)
  let L (c : V) := (J c).image leaves
  let N (c : V) := (L c).biUnion id
  let F (c : V) := U.filter (fun s => ∀ p ∈ s, G.Adj c p)
  let D (c : V) := (F c).filter (fun s => 1<s.card)
  have estimate (c : V) : (N c).card ≤ (J c).card + (D c).card := by
    have inc : L c ⊆ F c := by
      intro s hs
      obtain ⟨t,j,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨ht,eq⟩ := Finset.mem_filter.mp j
      exact Finset.mem_filter.mpr ⟨root t ht,eq ▸ adj t ht⟩
    have pieces (s) (hs : s ∈ F c) (size : 1<s.card) : ∃ a ∈ F c, ∃ b ∈ F c,
        a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s := by
      obtain ⟨su,inside⟩ := Finset.mem_filter.mp hs
      obtain ⟨a,au,b,bu,ltA,ltB,eq⟩ := split s su size
      have aa : a ⊆ s := eq ▸ Finset.subset_union_left
      have bb : b ⊆ s := eq ▸ Finset.subset_union_right
      exact ⟨a,Finset.mem_filter.mpr ⟨au,fun p h => inside p (aa h)⟩,
        b,Finset.mem_filter.mpr ⟨bu,fun p h => inside p (bb h)⟩,ltA,ltB,eq⟩
    exact (multi_root_union (F c) (L c) inc pieces).trans
      (Nat.add_le_add_right (Finset.card_image_le (s := J c) (f := leaves)) _)
  have separate : (K : Set V).PairwiseDisjoint D := by
    intro c _ d _ ne
    apply Finset.disjoint_left.mpr
    intro s sc sd
    have ac := (Finset.mem_filter.mp (Finset.mem_filter.mp sc).1).2
    have ad := (Finset.mem_filter.mp (Finset.mem_filter.mp sd).1).2
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (Finset.mem_filter.mp sc).2
    exact (sq c a d b (ac a ha) (ad a ha).symm (ad b hb) (ac b hb).symm).elim ne ab
  have numD : (∑ c ∈ K, (D c).card) ≤ (U.filter (fun s => 1<s.card)).card := by
    rw [←Finset.card_biUnion separate]
    apply Finset.card_le_card
    intro s hs
    obtain ⟨c,_,sc⟩ := Finset.mem_biUnion.mp hs
    have h := Finset.mem_filter.mp sc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.1).1,h.2⟩
  have count : (∑ c ∈ K, (J c).card)=T.card := by
    exact (Finset.card_eq_sum_card_fiberwise (f := center) (s := T) (t := K)
      (fun t ht => Finset.mem_image_of_mem center ht)).symm
  let A (c : V) := (N c).image (fun p => s(c,p))
  have all : E ⊆ K.biUnion A := by
    intro e he
    obtain ⟨t,ht,p,hp,rfl⟩ := edges e he
    refine Finset.mem_biUnion.mpr ⟨center t,Finset.mem_image_of_mem _ ht,
      Finset.mem_image.mpr ⟨p,Finset.mem_biUnion.mpr ⟨leaves t,?_,hp⟩,rfl⟩⟩
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,rfl⟩,rfl⟩
  have upper : E.card ≤ ∑ c ∈ K, (N c).card :=
    (Finset.card_le_card all).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum
      (fun c _ => Finset.card_image_le (s := N c) (f := fun p => s(c,p)))))
  have add := Finset.sum_le_sum (s := K) (fun c _ => estimate c)
  rw [Finset.sum_add_distrib,count] at add
  omega

end PlaneResearch.StarCounting
