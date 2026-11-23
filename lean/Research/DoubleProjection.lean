import Research.DegreeTwoOr
import Research.PlaneOrderThree

namespace PlaneResearch.InputDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection

/-- If every active point is in two or more rows, a uniform lower bound for all
one-point deletions gives two additional gates in the original circuit. -/
theorem lift_two {n r : ℕ} (S : Fin r → Finset (Fin n)) (rows : 0 < r)
    (two : ∀ i, 2 ≤ (S i).card) (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (active : ∀ p, degree S p = 0 ∨ 2 ≤ degree S p) (b : ℕ)
    (del : ∀ p, 2 ≤ degree S p → ∀ (D : Circuit) (o : Fin r → ℕ), FanInTwo D →
      (∀ i x, (Circuit.mk D.gates (o i)).eval (List.ofFn x) = sumRow ((S i).erase p) x) → b ≤ D.size)
    (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    b+2 ≤ C.size := by
  classical
  suffices main : ∀ l (gs : List Gate) (o : Fin r → ℕ), gs.length=l → FanInTwo ⟨gs,0⟩ →
      (∀ i x, (Circuit.mk gs (o i)).eval (List.ofFn x) = sumRow (S i) x) → b+2 ≤ gs.length from
    main _ C.gates out rfl hf hc
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro gs o len ok ev
    cases gs with
    | nil =>
      have sem (i : Fin r) (x : Fin n → Bool) :
          ((Circuit.mk [] 0).wires (List.ofFn x)).getD (o i) false = true ↔ ∃ p ∈ S i, x p = true := by
        change (Circuit.mk [] (o i)).eval (List.ofFn x) = true ↔ _
        rw [ev]; simp [sumRow]
      have z := (PlaneResearch.TripleSystems.Unrestricted.unrestricted_rows n r S two thin ⟨[],0⟩ o ok sem).1
      change r+_ ≤ 0 at z
      omega
    | cons g gs =>
      rcases head_reduction S two thin g gs o ok ev with ⟨hs,o',weak,hf',he⟩ | ⟨p,hs,o',weak,extra,hf',he⟩
      · have lt : hs.length < l := by simp only [List.length_cons] at len; omega
        have h := ih _ lt hs o' rfl hf' he
        simp only [List.length_cons]; omega
      · rcases active p with zero|used
        · have no (i : Fin r) : p ∉ S i := by
            intro pi
            have yes : 0 < degree S p := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pi⟩⟩
            omega
          have lt : hs.length < l := by simp only [List.length_cons] at len; omega
          have h := ih _ lt hs o' rfl hf' (fun i x => by simpa [Finset.erase_eq_of_notMem (no i)] using he i x)
          simp only [List.length_cons]; omega
        · have lower := del p used ⟨hs,0⟩ o' hf' he
          have save := extra used
          change b ≤ hs.length at lower
          simp only [List.length_cons]; omega

end PlaneResearch.InputDegree

namespace PlaneResearch.PlaneOrderThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection PlaneResearch.InputDegree

private lemma after_two (a b : Fin 13) (ab : a ≠ b) (D : Circuit) (o : Fin 13 → ℕ) (hf : FanInTwo D)
    (hc : ∀ i x, (Circuit.mk D.gates (o i)).eval (List.ofFn x) = sumRow (((lines i).erase a).erase b) x) :
    26 ≤ D.size := by
  let R i := ((lines i).erase a).erase b
  have size : ∀ i, 2 ≤ (R i).card :=
    (by decide +kernel : ∀ a b i : Fin 13, 2 ≤ (((lines i).erase a).erase b).card) a b
  have lin (i j) (ne : i ≠ j) : (R i ∩ R j).card ≤ 1 := by
    have sub (i) : R i ⊆ lines i := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    exact (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans
      ((by decide +kernel : ∀ i j : Fin 13, i ≠ j → (lines i ∩ lines j).card ≤ 1) i j ne)
  have cost : (∑ i, ((R i).card-1)) = 31 := (by decide +kernel : ∀ a b : Fin 13, a ≠ b →
    (∑ i, ((((lines i).erase a).erase b).card-1)) = 31) a b ab
  have excess : (∑ i, ((R i).card-3)) = 6 := (by decide +kernel : ∀ a b : Fin 13, a ≠ b →
    (∑ i, ((((lines i).erase a).erase b).card-3)) = 6) a b ab
  have h := rank_excess R size lin D o hf hc
  rw [cost,excess] at h
  omega

theorem deleted_twenty_eight (a : Fin 13) (D : Circuit) (o : Fin 13 → ℕ) (hf : FanInTwo D)
    (hc : ∀ i x, (Circuit.mk D.gates (o i)).eval (List.ofFn x) = sumRow ((lines i).erase a) x) :
    28 ≤ D.size := by
  let S i := (lines i).erase a
  have two : ∀ i, 2 ≤ (S i).card := (by decide +kernel : ∀ a i : Fin 13, 2 ≤ ((lines i).erase a).card) a
  have lin (i j) (ne : i ≠ j) : (S i ∩ S j).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter (Finset.erase_subset _ _) (Finset.erase_subset _ _))).trans
      ((by decide +kernel : ∀ i j : Fin 13, i ≠ j → (lines i ∩ lines j).card ≤ 1) i j ne)
  have degA (p : Fin 13) : degree S p = if p=a then 0 else 4 := (by decide +kernel :
    ∀ a p : Fin 13, degree (fun i => (lines i).erase a) p = if p=a then 0 else 4) a p
  apply lift_two S (by decide) two lin (fun p => by rw [degA]; split <;> decide) 26 _ D o hf hc
  intro p hit E oe ok ev
  have ne : a ≠ p := by rintro rfl; simp [degA] at hit
  exact after_two a p ne E oe ok ev

/-- Thirty gates are necessary for the full incidence matrix with unbounded negations. -/
theorem thirty (C : Circuit) (out : Fin 13 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (lines i) x) :
    30 ≤ C.size := by
  apply lift_two lines (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) 28 _ C out hf hc
  intro p _ D o ok ev
  exact deleted_twenty_eight p D o ok ev

end PlaneResearch.PlaneOrderThree
