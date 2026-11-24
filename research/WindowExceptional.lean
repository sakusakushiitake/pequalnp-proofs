import PEqualNP.Outside.L_meta_1594

namespace WindowExceptional

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1594

/-- At least two singleton inputs from S activate the wire. -/
def wide {n : ℕ} (C : Circuit) (S : Base n) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w => 2 ≤ ((supp C ∅ w) ∩ S).card

theorem wide_count {n : ℕ} (C : Circuit) (S : Base n) (w : ℕ) (mono : Mono C)
    (yes : ∀ p ∈ S, value C (fun v => decide (v ∈ (∅ : Base n) ∨ v=p)) w = true)
    (no : value C (bits (∅ : Base n)) w = false) :
    S.card ≤ (wide C S).card+1 := by
  classical
  let G := wide C S
  have loc (r) (hr : r ∈ G) := Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
  obtain ⟨B,apart,limit,transport⟩ := cut C mono G (fun r hr => loc r hr)
    (n+C.size) {w} (fun r _ hr => (loc r hr).2)
  let seen := fun r => (supp C (∅ : Base n) r) ∩ S
  have small (r) (hr : r ∈ B) : (seen r).card ≤ 1 := by
    by_contra! many
    have two : 2 ≤ (supp C (∅ : Base n) r).card :=
      (show 2 ≤ (seen r).card by omega).trans (Finset.card_le_card Finset.inter_subset_left)
    have gate := windowG_only_wire C (∅ : Base n) (Finset.univ : Base n) (by simp) r
      (Finset.subset_univ _) two
    exact Finset.disjoint_left.mp apart hr (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr gate,show 2 ≤ (seen r).card by omega⟩)
  have cover : S ⊆ B.biUnion seen := by
    intro p hp
    by_contra miss
    have step (r) (hr : r ∈ B) (hx : value C (fun v => decide (v ∈ (∅ : Base n) ∨ v=p)) r = true) :
        value C (bits (∅ : Base n)) r = true := by
      exact (miss (Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨(mem_supp C ∅ r p).mpr hx,hp⟩⟩)).elim
    have h := transport _ _ step w (by simp) (yes p hp)
    rw [no] at h
    contradiction
  have count := Finset.card_biUnion_le_card_mul B seen 1 small
  have upper := Finset.card_filter_le G (· < n+C.size)
  have lower := Finset.card_le_card cover
  simp only [mul_one] at count
  simp only [Finset.card_singleton] at limit
  change S.card ≤ G.card+1
  omega

/-- Any chosen row earns its full size; all other rows receive the ordinary light bound. -/
theorem exceptional {n m : ℕ} (S : Fin m → Base n) (C : Circuit) (o : Fin m → ℕ)
    (t k : ℕ) (anchor : Fin m) (hk : 2 ≤ k)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (light : Light (n:=n) C t k) :
    (∑ i, if i=anchor then (S i).card else min k (S i).card) ≤ C.gates.length+m := by
  classical
  let D := pin C t true
  let pay := fun i => if i=anchor then wide D (S i) else windowG D ∅ (S i)
  have aswide (i r) (hr : r ∈ pay i) : 2 ≤ ((supp D (∅ : Base n) r) ∩ S i).card := by
    by_cases eq : i=anchor
    · exact (Finset.mem_filter.mp (show r ∈ wide D (S i) by simpa [pay,eq] using hr)).2
    · obtain ⟨sub,two⟩ := (Finset.mem_filter.mp
        (show r ∈ windowG D ∅ (S i) by simpa [pay,eq] using hr)).2
      simpa [Finset.inter_eq_left.mpr sub] using two
  have nolap (i j : Fin m) (ne : i≠j) (ordinary : j≠anchor) : Disjoint (pay i) (pay j) := by
    apply Finset.disjoint_left.mpr
    intro r hi hj
    have sj := (Finset.mem_filter.mp (show r ∈ windowG D ∅ (S j) by simpa [pay,ordinary] using hj)).2.1
    have sub : (supp D (∅ : Base n) r) ∩ S i ⊆ S i ∩ S j :=
      Finset.subset_inter Finset.inter_subset_right (Finset.inter_subset_left.trans sj)
    have low := aswide i r hi
    have high := (Finset.card_le_card sub).trans (thin i j ne)
    omega
  have apart : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint pay := by
    intro i _ j _ ne
    by_cases h : j=anchor
    · exact (nolap j i ne.symm (fun hi => ne (hi.trans h.symm))).symm
    · exact nolap i j ne h
  have each (i) : (if i=anchor then (S i).card else min k (S i).card) ≤ (pay i).card+1 := by
    by_cases eq : i=anchor
    · simp only [pay,eq,ite_true]
      apply wide_count D (S anchor) (o anchor) (pin_mono C t true legal one)
      · intro p hp
        have e : (fun v : Fin n => decide (v ∈ (∅ : Base n) ∨ v=p)) = bits {p} := by funext v; simp [bits]
        rw [e]
        have hsmall := light (bits {p}) (by rw [true_count_bits,Finset.card_singleton]; omega)
        rw [show D=pin C t true from rfl,pin_value C t true _ _ (Or.inr hsmall),out]
        exact decide_eq_true ⟨p,hp,by simp [bits]⟩
      · have hsmall := light (bits (∅ : Base n)) (by rw [true_count_bits,Finset.card_empty]; omega)
        rw [show D=pin C t true from rfl,pin_value C t true _ _ (Or.inr hsmall),out]
        simp [bits]
    · simp only [pay,eq,ite_false]
      exact light_count C t k legal one light hk (S i) (o i) (out i)
  have cover : Finset.univ.biUnion pay ⊆ Finset.Ico n (n+D.size) := by
    intro r hr
    obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp hr
    by_cases e : i=anchor
    · exact (Finset.mem_filter.mp (show r ∈ wide D (S i) by simpa [pay,e] using h)).1
    · exact (Finset.mem_filter.mp (show r ∈ windowG D ∅ (S i) by simpa [pay,e] using h)).1
  have total := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => each i)
  rw [Finset.sum_add_distrib,← Finset.card_biUnion apart] at total
  have cap := Finset.card_le_card cover
  rw [show D.size = C.size from pin_size C t true] at cap
  simp at cap
  simpa [Circuit.size] using total.trans (Nat.add_le_add_right cap _)

end WindowExceptional
