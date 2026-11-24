import PEqualNP.Outside.L_meta_1594
import PEqualNP.Outside.L_meta_1595

namespace WindowRefund
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1595

def big {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) :=
  Finset.univ.filter fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card

noncomputable def refund {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (Y : Finset (Fin n)) :
    Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g =>
    (∃ i, ∀ p, value C (fun v => decide (v=p)) (n+g.val) = true ↔ p ∈ S i) ∧
    (∃ i, Disjoint (S i) Y ∧ ∀ p, p ∉ Y →
      (value C (fun v => decide (v ∈ Y ∨ v=p)) (n+g.val) = true ↔ p ∈ S i))

theorem distinct_refunds {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (Y : Finset (Fin n)) (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (big S Y).card ≤ (refund S C Y).card := by
  classical
  have single (i) (p : Fin n) : value C (fun v => decide (v=p)) (o i) = true ↔ p ∈ S i := by
    rw [out]; simp
  let dest := (refund S C Y).image (fun g : Fin C.gates.length => n+g.val)
  refine (Finset.card_le_card_of_injOn o (t:=dest) ?_ ?_).trans Finset.card_image_le
  · intro i hi
    obtain ⟨di,two⟩ := (Finset.mem_filter.mp hi).2
    have lower : n ≤ o i := by
      by_contra! raw
      let r : Fin n := ⟨o i,raw⟩
      have sub : S i ⊆ {r} := by
        intro p hp
        have yes := (single i p).mpr hp
        change value C (fun v => decide (v=p)) r.val = true at yes
        rw [input_value] at yes
        exact Finset.mem_singleton.mpr (of_decide_eq_true yes).symm
      have one := Finset.card_le_card sub
      simp at one
      omega
    have upper : o i < n+C.size := by
      by_contra! far
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (S i).card)
      have yes := (single i p).mpr hp
      rw [missing_value C _ _ far] at yes
      contradiction
    let g : Fin C.gates.length := ⟨o i-n,by change o i<n+C.gates.length at upper; omega⟩
    have eg : n+g.val=o i := by dsimp [g]; omega
    refine Finset.mem_image.mpr ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,eg⟩
    rw [eg]
    refine ⟨⟨i,single i⟩,i,di,?_⟩
    intro p _
    rw [out,decide_eq_true_eq]
    constructor
    · rintro ⟨q,qi,hy⟩
      rcases of_decide_eq_true hy with qy | rfl
      · exact (Finset.disjoint_left.mp di qi qy).elim
      · exact qi
    · intro hp
      exact ⟨p,hp,by simp⟩
  · intro i hi j _ eq
    by_contra ne
    have same : S i = S j := by ext p; rw [← single i p,← single j p,eq]
    have lim := thin i j ne
    rw [← same,Finset.inter_self] at lim
    have two := ((Finset.mem_filter.mp hi).2).2
    omega

open PEqualNP.Outside.L_meta_1594 (singletonGates light_count charge_card_le Legal Only Light)

theorem total_light {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t k : ℕ) (hk : 2 ≤ k)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : Light (n:=n) C t k) : ∑ i, min k (S i).card ≤ C.gates.length+m := by
  classical
  let F := fun i => singletonGates C (S i)
  have apart : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint F := by
    intro i _ j _ ne
    change Disjoint (F i) (F j)
    apply Finset.disjoint_left.mpr
    intro g gi gj
    obtain ⟨si,two⟩ := (Finset.mem_filter.mp gi).2
    obtain ⟨sj,_⟩ := (Finset.mem_filter.mp gj).2
    have lim := (Finset.card_le_card (Finset.subset_inter si sj)).trans (thin i j ne)
    omega
  have each (i) : min k (S i).card ≤ (F i).card+1 :=
    (light_count C t k legal one small hk (S i) (o i) (out i)).trans
      (Nat.add_le_add_right (charge_card_le C t k small hk (S i)) 1)
  have sum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => each i)
  rw [Finset.sum_add_distrib,← Finset.card_biUnion apart] at sum
  have cap := Finset.card_le_univ (Finset.univ.biUnion F)
  simp only [Fintype.card_fin] at cap
  simpa using sum.trans (Nat.add_le_add_right cap _)

theorem heavy_excess {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : Light (n:=n) C t Y.card)
    (room : (∑ i, if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤ (big S Y).card) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.gates.length+(refund S C Y).card+m := by
  classical
  have l := total_light S C o t Y.card hk thin legal one out small
  have r := distinct_refunds S C o Y thin out
  have each (i) : (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) =
      min Y.card (S i).card + (if Disjoint (S i) Y then (S i).card-Y.card else 0) := by
    by_cases dis : Disjoint (S i) Y <;> simp [dis] <;> omega
  simp_rw [each, Finset.sum_add_distrib]
  omega

/-- Each disjoint row may have one more element than the light window width. -/
theorem width_plus_one {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : Light (n:=n) C t Y.card)
    (width : ∀ i, Disjoint (S i) Y → (S i).card ≤ Y.card+1) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.gates.length+(refund S C Y).card+m := by
  classical
  apply heavy_excess S C o t Y hk thin legal one out small
  have row (i) : (if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤
      (if i ∈ big S Y then 1 else 0) := by
    by_cases dis : Disjoint (S i) Y
    · have cap := width i dis
      by_cases large : 2 ≤ (S i).card <;> simp [dis,big,large] <;> omega
    · simp [dis]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => row i)
  simpa using h

end WindowRefund
