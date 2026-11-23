import Research.BicliqueStar

namespace PlaneResearch.StarCounting

/-- The union of the requested sets has at most one point per root and one
additional point per distinct nonsingleton set built by a binary union. -/
theorem multi_root_union {V : Type*} [DecidableEq V] (F R : Finset (Finset V)) (roots : R ⊆ F)
    (split : ∀ s ∈ F, 1<s.card → ∃ a ∈ F, ∃ b ∈ F, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    (R.biUnion id).card ≤ R.card + (F.filter (fun s => 1<s.card)).card := by
  classical
  suffices main : ∀ l (F R : Finset (Finset V)), F.card=l → R ⊆ F →
      (∀ s ∈ F, 1<s.card → ∃ a ∈ F, ∃ b ∈ F, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) →
      (R.biUnion id).card ≤ R.card + (F.filter (fun s => 1<s.card)).card from main _ F R rfl roots split
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro F R length roots split
    let D := F.filter (fun s => 1<s.card)
    by_cases any : D.Nonempty
    · obtain ⟨s,sd,maximal⟩ := Finset.exists_max_image D Finset.card any
      obtain ⟨sf,big⟩ := Finset.mem_filter.mp sd
      have less : (F.erase s).card<l := by rw [←length]; exact Finset.card_erase_lt_of_mem sf
      have still (t) (ht : t ∈ F.erase s) (sz : 1<t.card) :
          ∃ a ∈ F.erase s, ∃ b ∈ F.erase s, a.card<t.card ∧ b.card<t.card ∧ a ∪ b=t := by
        obtain ⟨_,tf⟩ := Finset.mem_erase.mp ht
        have bound := maximal t (Finset.mem_filter.mpr ⟨tf,sz⟩)
        obtain ⟨a,af,b,bf,ltA,ltB,eq⟩ := split t tf sz
        refine ⟨a,Finset.mem_erase.mpr ⟨?_,af⟩,b,Finset.mem_erase.mpr ⟨?_,bf⟩,ltA,ltB,eq⟩
        · rintro rfl; omega
        · rintro rfl; omega
      have deq : (F.erase s).filter (fun t => 1<t.card) = D.erase s := by ext; simp [D,and_assoc]
      have paid := Finset.card_erase_add_one sd
      change _ ≤ R.card+D.card
      by_cases sr : s ∈ R
      · obtain ⟨a,af,b,bf,ltA,ltB,union⟩ := split s sf big
        let Q := insert a (insert b (R.erase s))
        have inc : Q ⊆ F.erase s := by
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact Finset.mem_erase.mpr ⟨fun e => (Nat.ne_of_lt ltA) (congrArg Finset.card e),af⟩
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact Finset.mem_erase.mpr ⟨fun e => (Nat.ne_of_lt ltB) (congrArg Finset.card e),bf⟩
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1,roots (Finset.mem_erase.mp ht).2⟩
        have cover : R.biUnion id ⊆ Q.biUnion id := by
          intro x hx
          obtain ⟨t,tr,xt⟩ := Finset.mem_biUnion.mp hx
          by_cases eq : t=s
          · subst t
            change x ∈ s at xt
            rw [←union] at xt
            rcases Finset.mem_union.mp xt with ha|hb
            · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_insert_self ..,ha⟩
            · exact Finset.mem_biUnion.mpr ⟨b,by simp [Q],hb⟩
          · exact Finset.mem_biUnion.mpr ⟨t,by simp [Q,tr,eq],xt⟩
        have budget : Q.card ≤ R.card+1 := by
          have h₁ := Finset.card_insert_le a (insert b (R.erase s))
          have h₂ := Finset.card_insert_le b (R.erase s)
          have h₃ := Finset.card_erase_add_one sr
          change (insert a (insert b (R.erase s))).card ≤ _
          omega
        have h := ih _ less (F.erase s) Q rfl inc still
        rw [deq] at h
        have := Finset.card_le_card cover
        omega
      · have inc : R ⊆ F.erase s := fun t ht => Finset.mem_erase.mpr ⟨fun e => sr (e ▸ ht),roots ht⟩
        have h := ih _ less (F.erase s) R rfl inc still
        rw [deq] at h
        omega
    · have small (s : Finset V) (sr : s ∈ R) : s.card ≤ 1 := by
        by_contra! big
        exact any ⟨s,Finset.mem_filter.mpr ⟨roots sr,big⟩⟩
      have a : (R.biUnion id).card ≤ ∑ s ∈ R, s.card := Finset.card_biUnion_le
      have b : (∑ s ∈ R, s.card) ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum small
      simp at b
      omega

/-- Count reads leaving wires with empty singleton support. A productive AND
reads only positive-support wires. A gate returning to positive support has
room for at most one empty-support predecessor. -/
theorem zero_read_count {V : Type*} [DecidableEq V] (Z A M : Finset V) (roots : A ⊆ Z) (out : V) (parents : V → Finset V)
    (uses : ∀ i ∈ Z, i=out ∨ (∃ j ∈ Z \ A, i ∈ parents j) ∨ ∃ j ∈ M, i ∈ parents j)
    (binary : ∀ j ∈ Z \ A, (parents j ∩ Z).card ≤ 2)
    (mixed : ∀ j ∈ M, (parents j ∩ Z).card ≤ 1) : A.card ≤ (Z \ A).card + M.card + 1 := by
  let N (j : V) := parents j ∩ Z
  have cover : Z ⊆ ({out} ∪ (Z \ A).biUnion N) ∪ M.biUnion N := by
    intro i hi
    rcases uses i hi with rfl|⟨j,hj,h⟩|⟨j,hj,h⟩
    · simp
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨h,hi⟩⟩))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨h,hi⟩⟩)
  have a := Finset.card_le_card cover
  have b := Finset.card_union_le ({out} ∪ (Z \ A).biUnion N) (M.biUnion N)
  have c := Finset.card_union_le ({out} : Finset V) ((Z \ A).biUnion N)
  have z : ((Z \ A).biUnion N).card ≤ (Z \ A).card*2 := by
    apply Finset.card_biUnion_le.trans
    simpa using (Finset.sum_le_sum binary : (∑ i ∈ Z \ A, (parents i ∩ Z).card) ≤ ∑ _i ∈ Z \ A, 2)
  have m : (M.biUnion N).card ≤ M.card := by
    apply Finset.card_biUnion_le.trans
    simpa using (Finset.sum_le_sum mixed : (∑ i ∈ M, (parents i ∩ Z).card) ≤ ∑ _i ∈ M, 1)
  have eq := Finset.card_sdiff_add_card_eq_card roots
  simp only [Finset.card_singleton] at c
  omega

end PlaneResearch.StarCounting
