import PEqualNP.Outside.L_meta_1594
import PEqualNP.Outside.L_meta_1595

namespace WindowIndirect

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1595
open PEqualNP.Outside.L_meta_1594 (Legal Only Light singletonGates light_count charge_card_le)

def pool {n : ℕ} (C : Circuit) (B S : Finset (Fin n)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun g => supp C B (n+g.val) ⊆ S ∧ 2 ≤ (supp C B (n+g.val)).card

/-- Gates with two large supports that agree on at most one point. -/
def crossings {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun g =>
    2 ≤ (supp C (∅ : Finset (Fin n)) (n+g.val)).card ∧
    2 ≤ (supp C Y (n+g.val)).card ∧
    ((supp C ∅ (n+g.val)) ∩ (supp C Y (n+g.val))).card ≤ 1

lemma separate {n m : ℕ} (C : Circuit) (B : Finset (Fin n)) (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (i j : Fin m) (ne : i ≠ j) :
    Disjoint (pool C B (S i)) (pool C B (S j)) := by
  apply Finset.disjoint_left.mpr
  intro g gi gj
  obtain ⟨si,two⟩ := (Finset.mem_filter.mp gi).2
  obtain ⟨sj,_⟩ := (Finset.mem_filter.mp gj).2
  have lim := (Finset.card_le_card (Finset.subset_inter si sj)).trans (thin i j ne)
  omega

lemma heavy_card {n : ℕ} (C : Circuit) (Y S : Finset (Fin n)) (di : Disjoint S Y) :
    (asg C Y S).card ≤ (pool C Y S).card := by
  let emb : Fin C.gates.length ↪ ℕ := ⟨fun g => n+g.val,fun a b eq => Fin.ext (Nat.add_left_cancel eq)⟩
  rw [← Finset.card_map (f:=emb)]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨⟨lo,hi⟩,soundW,two⟩ := (mem_asg C Y S w).mp hw
  let g : Fin C.gates.length := ⟨w-n,by unfold Circuit.size at hi; omega⟩
  have addr : n+g.val=w := by dsimp [g]; omega
  refine Finset.mem_map.mpr ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ g,?_⟩,addr⟩
  rw [addr]
  refine ⟨?_,two⟩
  intro p hp
  obtain ⟨q,qs,hy⟩ := soundW _ (fun _ hv => decide_eq_true (Or.inl hv)) ((mem_supp C Y w p).mp hp)
  rcases of_decide_eq_true hy with qy | rfl
  · exact (Finset.disjoint_left.mp di qs qy).elim
  · exact qs

theorem bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : Light (n:=n) C t Y.card)
    (off : value C (fun v => decide (v ∈ Y)) (n+t) = false) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.gates.length + (crossings C Y).card + m := by
  classical
  let H := fun i => if Disjoint (S i) Y then pool C Y (S i) else ∅
  let L := fun i => if Disjoint (S i) Y then ∅ else pool C ∅ (S i)
  have hsub (i) : H i ⊆ pool C Y (S i) := by by_cases d : Disjoint (S i) Y <;> simp [H,d]
  have lsub (i) : L i ⊆ pool C ∅ (S i) := by by_cases d : Disjoint (S i) Y <;> simp [L,d]
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint H :=
    fun i _ j _ ne => (separate C Y S thin i j ne).mono (hsub i) (hsub j)
  have lpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint L :=
    fun i _ j _ ne => (separate C ∅ S thin i j ne).mono (lsub i) (lsub j)
  have each (i) : (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      (H i).card+(L i).card+1 := by
    by_cases d : Disjoint (S i) Y
    · simp only [d,ite_true,H,L,Finset.card_empty,Nat.add_zero]
      apply (card_le C Y (S i) t legal one off (o i) d.symm ?_ ?_).trans
        (Nat.add_le_add_right (heavy_card C Y (S i) d) 1)
      · intro x _ hx
        exact of_decide_eq_true ((out i x).symm.trans hx)
      · intro p hp
        exact (out i _).trans (decide_eq_true ⟨p,hp,by simp⟩)
    · simp only [d,ite_false,H,L,Finset.card_empty,Nat.zero_add]
      exact (light_count C t Y.card legal one small hk (S i) (o i) (out i)).trans
        (Nat.add_le_add_right (charge_card_le C t Y.card small hk (S i)) 1)
  let A := Finset.univ.biUnion H
  let B := Finset.univ.biUnion L
  have both : A ∩ B ⊆ crossings C Y := by
    intro g hg
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hg).1
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hg).2
    have ne : j ≠ i := by
      rintro rfl
      by_cases di : Disjoint (S j) Y
      · simp [L,di] at hj
      · simp [H,di] at hi
    obtain ⟨hs,htwo⟩ := (Finset.mem_filter.mp (hsub i hi)).2
    obtain ⟨ls,ltwo⟩ := (Finset.mem_filter.mp (lsub j hj)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ltwo,htwo,
      (Finset.card_le_card (Finset.inter_subset_inter ls hs)).trans (thin j i ne)⟩
  have sum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => each i)
  simp only [Finset.sum_add_distrib,← Finset.card_biUnion hpair,← Finset.card_biUnion lpair,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at sum
  change _ ≤ A.card+B.card+m at sum
  have eq := Finset.card_union_add_card_inter A B
  have cap := Finset.card_le_univ (A ∪ B)
  simp only [Fintype.card_fin] at cap
  have boundCross := Finset.card_le_card both
  omega

lemma not_crossing_of_growth {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (g : Fin C.gates.length)
    (inc : supp C (∅ : Finset (Fin n)) (n+g.val) ⊆ supp C Y (n+g.val)) : g ∉ crossings C Y := by
  intro hg
  obtain ⟨two,_,one⟩ := (Finset.mem_filter.mp hg).2
  rw [Finset.inter_eq_left.mpr inc] at one
  omega

theorem after_not {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n)) (legal : Legal C)
    (one : Only C t) (off : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (g : Fin C.gates.length) (hg : g ∈ crossings C Y) : t < g.val := by
  classical
  by_contra! earlier
  have earlier_mono (w : ℕ) (lt : w<n+t) (x y : Fin n → Bool) (xy : ∀ p, x p = true → y p = true) :
      value C x w = true → value C y w = true := by
    have h := PEqualNP.Outside.L_meta_1594.value_mono _ (PEqualNP.Outside.L_meta_1594.pin_mono C t false legal one)
      x y xy w
    rw [PEqualNP.Outside.L_meta_1594.pin_value C t false x w (Or.inl lt),
        PEqualNP.Outside.L_meta_1594.pin_value C t false y w (Or.inl lt)] at h
    exact h
  have hi : n+g.val<n+C.size := Nat.add_lt_add_left g.isLt n
  have lo : n ≤ n+g.val := by omega
  have ops := legal (C.gates[g.val]) (List.getElem_mem g.isLt)
  by_cases neg : C.gates[g.val].op = GateOp.not
  · have atT : g.val=t := one g neg
    have emp : supp C Y (n+g.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have no := not_false C Y (n+g.val) lo hi (by simpa using neg) (by simpa [atT] using off)
        (fun v => decide (v ∈ Y ∨ v=p)) (fun r hr => earlier_mono r (by omega) _ _
          (fun q hq => decide_eq_true (Or.inl (of_decide_eq_true hq))))
      have yes := (mem_supp C Y _ p).mp hp
      rw [no] at yes
      contradiction
    have two := (Finset.mem_filter.mp hg).2.2.1
    simp [emp] at two
  · have ao : C.gates[g.val].op = GateOp.and ∨ C.gates[g.val].op = GateOp.or := by
      rcases ops.1 with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · contradiction
    obtain ⟨P,_,before,lift⟩ := gate_inputs C (n+g.val) lo hi (by simpa using ao) (by simpa using ops.2)
    apply not_crossing_of_growth C Y g _ hg
    intro p hp
    apply (mem_supp C Y _ p).mpr
    apply lift _ _ _ ((mem_supp C ∅ _ p).mp hp)
    intro w hw
    apply earlier_mono w (by have := before w hw; omega)
    intro v yes
    rcases of_decide_eq_true yes with empty | eq
    · simp at empty
    · exact decide_eq_true (Or.inr eq)

lemma precontinuity {n : ℕ} (C : Circuit) (t : ℕ) (legal : Legal C) (one : Only C t)
    (w : ℕ) (lt : w<n+t) (x y : Fin n → Bool) (inc : ∀ q, x q = true → y q = true) :
    value C x w = true → value C y w = true := by
  have h := PEqualNP.Outside.L_meta_1594.value_mono _ (PEqualNP.Outside.L_meta_1594.pin_mono C t false legal one)
    x y inc w
  rw [PEqualNP.Outside.L_meta_1594.pin_value C t false x w (Or.inl lt),
      PEqualNP.Outside.L_meta_1594.pin_value C t false y w (Or.inl lt)] at h
  exact h

lemma flag_values {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (legal : Legal C) (one : Only C t) (small : Light (n:=n) C t Y.card)
    (off : value C (fun v => decide (v ∈ Y)) (n+t) = false) :
    (∀ p : Fin n, value C (fun v => decide (v ∈ (∅ : Finset (Fin n)) ∨ v=p)) (n+t) = true) ∧
    (∀ p : Fin n, value C (fun v => decide (v ∈ Y ∨ v=p)) (n+t) = false) := by
  classical
  have emp : value C (fun _ : Fin n => false) (n+t) = true :=
    small (fun _ : Fin n => false) (by
      have hz : (Finset.univ.filter fun _ : Fin n => false = true) = ∅ := by ext; simp
      rw [hz, Finset.card_empty]
      omega)
  have valid : t < C.gates.length := by
    by_contra! no
    rw [missing_value C _ _ (by unfold Circuit.size; omega)] at emp
    contradiction
  have lo : n ≤ n+t := by omega
  have hi : n+t < n+C.size := by unfold Circuit.size; omega
  have neg : C.gates[t].op = GateOp.not := by
    obtain ⟨op,arity⟩ := legal C.gates[t] (List.getElem_mem valid)
    by_contra no
    have ao : C.gates[t].op = GateOp.and ∨ C.gates[t].op = GateOp.or := by
      rcases op with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · contradiction
    obtain ⟨P,_,early,step⟩ := gate_inputs C (n+t) lo hi (by simpa using ao) (by simpa using arity)
    have v := step (fun _ : Fin n => false) (fun v => decide (v ∈ Y)) (fun w hw =>
      precontinuity C t legal one w (early w hw) _ _ (by simp)) emp
    rw [off] at v
    contradiction
  constructor
  · intro p
    apply small
    have eq : Finset.univ.filter (fun v : Fin n => decide (v ∈ (∅ : Finset (Fin n)) ∨ v=p) = true) = {p} := by
      ext v; simp
    rw [eq,Finset.card_singleton]
    omega
  · intro p
    apply not_false C Y (n+t) lo hi (by simpa using neg) off
    intro r hr
    apply precontinuity C t legal one r hr
    exact fun q h => decide_eq_true (Or.inl (of_decide_eq_true h))

lemma excludes_reader {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (legal : Legal C) (one : Only C t) (small : Light (n:=n) C t Y.card)
    (off : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (g : Fin C.gates.length) (hg : g ∈ crossings C Y) : n+t ∉ (C.gates.get g).inputs := by
  classical
  intro reads
  have later := after_not C t Y legal one off g hg
  have lt : n+t<n+g.val := by omega
  obtain ⟨light,heavy⟩ := flag_values C t Y hk legal one small off
  let inputs (x : Fin n → Bool) := (C.gates.get g).inputs.map (fun r => if r<n+g.val then value C x r else false)
  have hit (x : Fin n → Bool) : value C x (n+t) ∈ inputs x := by
    have h := List.mem_map_of_mem (f:=fun r => if r<n+g.val then value C x r else false) reads
    simpa only [lt,ite_true] using h
  have evalAt (x : Fin n → Bool) : value C x (n+g.val) = (C.gates.get g).op.eval (inputs x) := by
    have h := gate_value C x (n+g.val) (by omega) (Nat.add_lt_add_left g.isLt n)
    simpa [inputs,List.get_eq_getElem] using h
  obtain ⟨op,_⟩ := legal (C.gates.get g) (List.get_mem ..)
  rcases op with ha | ho | hn
  · have empty : supp C Y (n+g.val)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := (mem_supp C Y _ p).mp hp
      rw [evalAt,ha] at h
      have zero := hit (fun v => decide (v ∈ Y ∨ v=p))
      rw [heavy p] at zero
      exact Bool.noConfusion ((List.all_eq_true.mp h) false zero)
    have two := (Finset.mem_filter.mp hg).2.2.1
    simp [empty] at two
  · have full : supp C (∅ : Finset (Fin n)) (n+g.val) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      apply (mem_supp C ∅ _ p).mpr
      rw [evalAt,ho]
      apply List.any_eq_true.mpr
      have yes := hit (fun v => decide (v ∈ (∅ : Finset (Fin n)) ∨ v=p))
      rw [light p] at yes
      exact ⟨true,yes,rfl⟩
    obtain ⟨_,two,lim⟩ := (Finset.mem_filter.mp hg).2
    rw [full,Finset.univ_inter] at lim
    omega
  · have eq := one g hn
    omega


theorem indirect_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n)) (hk : 2 ≤ Y.card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (legal : Legal C) (one : Only C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : Light (n:=n) C t Y.card) (off : value C (fun v => decide (v ∈ Y)) (n+t) = false) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ C.gates.length +
      (Finset.univ.filter (fun g : Fin C.gates.length => t < g.val ∧ n+t ∉ (C.gates.get g).inputs ∧ ∀ i, o i ≠ n+g.val)).card + m := by
  classical
  have sub : crossings C Y ⊆ Finset.univ.filter (fun g : Fin C.gates.length => t < g.val ∧ n+t ∉ (C.gates.get g).inputs ∧ ∀ i, o i ≠ n+g.val) := by
    intro g hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,after_not C t Y legal one off g hg,excludes_reader C t Y hk legal one small off g hg,?_⟩
    intro i eq
    apply not_crossing_of_growth C Y g _ hg
    intro p hp
    have yes := (mem_supp C ∅ _ p).mp hp
    rw [← eq,out,decide_eq_true_eq] at yes
    obtain ⟨q,qs,hq⟩ := yes
    apply (mem_supp C Y _ p).mpr
    rw [← eq,out,decide_eq_true_eq]
    have same : q=p := by simpa using hq
    exact ⟨q,qs,decide_eq_true (Or.inr same)⟩
  exact (bound S C o t Y hk thin legal one out small off).trans (by have := Finset.card_le_card sub; omega)

end WindowIndirect
