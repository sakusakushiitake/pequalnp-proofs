import PEqualNP.Outside.L_meta_1595

namespace WindowHeavyReserve

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1595


def mask {n : ℕ} (Y : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ Y)

def losses {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Y.filter fun p => value C (mask Y) w = true ∧ value C (mask (Y.erase p)) w = false

def reserve {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w => 2 ≤ (losses C Y w).card

theorem losses_small {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ)
    (h : w ∉ reserve C Y) : (losses C Y w).card ≤ 1 := by
  classical
  by_contra! many
  apply h
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_,?_⟩,by omega⟩
  · by_contra! raw
    let q : Fin n := ⟨w,raw⟩
    have small : losses C Y w ⊆ {q} := by
      intro p hp
      obtain ⟨_,atY,minus⟩ := Finset.mem_filter.mp hp
      change value C (mask Y) q.val = true at atY
      change value C (mask (Y.erase p)) q.val = false at minus
      simp only [input_value,mask,decide_eq_true_eq,decide_eq_false_iff_not,Finset.mem_erase] at atY minus
      exact Finset.mem_singleton.mpr (by by_contra h; exact minus ⟨Ne.symm h,atY⟩)
    have smallCard := Finset.card_le_card small
    simp at smallCard
    omega
  · by_contra! beyond
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (losses C Y w).card)
    have yes := (Finset.mem_filter.mp hp).2.1
    rw [missing_value C _ _ beyond] at yes
    contradiction

theorem sensitivity_count {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (off : value C (mask Y) (n+t) = false) (target : ℕ)
    (atY : value C (mask Y) target = true)
    (minus : ∀ p ∈ Y, value C (mask (Y.erase p)) target = false) :
    Y.card ≤ (reserve C Y).card+1 := by
  classical
  let G := reserve C Y
  have step (w) (hw : w ∈ G) := by
    obtain ⟨pool,many⟩ := Finset.mem_filter.mp hw
    obtain ⟨low,high⟩ := Finset.mem_Ico.mp pool
    have idx : w-n<C.gates.length := by change w<n+C.gates.length at high; omega
    obtain ⟨op,arity⟩ := ops C.gates[w-n] (List.getElem_mem idx)
    have ao : C.gates[w-n].op = GateOp.and ∨ C.gates[w-n].op = GateOp.or := by
      rcases op with a | b | no
      · exact Or.inl a
      · exact Or.inr b
      have idt := unique ⟨w-n,idx⟩ no
      change w-n=t at idt
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (losses C Y w).card)
      have yes := (Finset.mem_filter.mp hp).2.1
      rw [show w=n+t by omega,off] at yes
      contradiction
    exact gate_inputs C w low high ao arity
  obtain ⟨B,apart,bc,cutw⟩ := cut C G step (n+C.size) {target}
    (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2)
  have cover : Y ⊆ B.biUnion (losses C Y) := by
    intro p hp
    by_contra missing
    have lift (w) (hw : w ∈ B) (yes : value C (mask Y) w = true) :
        value C (mask (Y.erase p)) w = true := by
      cases eq : value C (mask (Y.erase p)) w
      · exact (missing (Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨hp,yes,eq⟩⟩)).elim
      · rfl
    have yes := cutw _ _ lift target (by simp) atY
    rw [minus p hp] at yes
    contradiction
  have size := Finset.card_biUnion_le_card_mul B (losses C Y) 1
    (fun w hw => losses_small C Y w (Finset.disjoint_left.mp apart hw))
  have bound := (Finset.card_le_card cover).trans (by simpa using size)
  have f := Finset.card_filter_le G (· < n+C.size)
  simp only [Finset.card_singleton] at bc
  change Y.card ≤ G.card+1
  omega

/-- Disjoint rows pay their full sizes. Each other row pays at most two.
No assumption about the NOT value on small inputs or about gate ordering is needed. -/
theorem bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (off : value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min 2 (S i).card) + (reserve C Y).card ≤ C.gates.length+m := by
  classical
  let pool := Finset.Ico n (n+C.size)
  let heavy (i : Fin m) := asg C Y (S i)
  let light (i : Fin m) : Finset ℕ := if 2 ≤ (S i).card then {o i} else ∅
  let pay (i : Fin m) := if Disjoint (S i) Y then heavy i else light i
  have single (i) (p : Fin n) : value C (fun v => decide (v=p)) (o i) = true ↔ p ∈ S i := by
    rw [out]
    simp
  have isgate (i) (large : 2 ≤ (S i).card) : o i ∈ pool := by
    apply Finset.mem_Ico.mpr
    constructor
    · by_contra! raw
      let p : Fin n := ⟨o i,raw⟩
      have sub : S i ⊆ {p} := by
        intro r hr
        have v := (single i r).mpr hr
        change value C (fun u => decide (u=r)) p.val = true at v
        rw [input_value] at v
        exact Finset.mem_singleton.mpr (of_decide_eq_true v).symm
      have := Finset.card_le_card sub
      simp at this
      omega
    · by_contra! far
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (S i).card)
      have yes := (single i p).mpr hp
      rw [missing_value C _ _ far] at yes
      contradiction
  have data (i w) (hw : w ∈ heavy i) := (mem_asg C Y (S i) w).mp hw
  have capture (i) (dis : Disjoint (S i) Y) (w) (hw : w ∈ heavy i) :
      supp C Y w ⊆ S i := by
    intro p hp
    have yes := (mem_supp C Y w p).mp hp
    obtain ⟨a,ha,hy⟩ := (data i w hw).2.1 _ (fun v hv => decide_eq_true (Or.inl hv)) yes
    rcases of_decide_eq_true hy with ay | rfl
    · exact (Finset.disjoint_left.mp dis ha ay).elim
    · exact ha
  have separateHH (i j) (ne : i ≠ j) (di : Disjoint (S i) Y) (dj : Disjoint (S j) Y) :
      Disjoint (heavy i) (heavy j) := by
    apply Finset.disjoint_left.mpr
    intro w wi wj
    have sub := Finset.subset_inter (capture i di w wi) (capture j dj w wj)
    have lim := (Finset.card_le_card sub).trans (thin i j ne)
    have two := (data i w wi).2.2
    omega
  have separateHL (i j) (di : Disjoint (S i) Y) (dj : ¬ Disjoint (S j) Y) :
      Disjoint (heavy i) (light j) := by
    apply Finset.disjoint_left.mpr
    intro w wi wj
    by_cases big : 2 ≤ (S j).card
    · have eq : w = o j := by simpa [light,big] using wj
      subst w
      obtain ⟨p,pj,py⟩ := Finset.not_disjoint_iff.mp dj
      let y := fun v : Fin n => decide (v ∈ Y)
      have yes : value C y (o j) = true := (out j y).trans (decide_eq_true ⟨p,pj,decide_eq_true py⟩)
      obtain ⟨v,vi,vy⟩ := (data i _ wi).2.1 y (fun _ h => decide_eq_true h) yes
      exact Finset.disjoint_left.mp di vi (of_decide_eq_true vy)
    · simpa [light,big] using wj
  have separateLL (i j) (ne : i ≠ j) : Disjoint (light i) (light j) := by
    by_cases a : 2 ≤ (S i).card <;> by_cases b : 2 ≤ (S j).card
    · simp only [light,a,b,ite_true,Finset.disjoint_singleton_left,Finset.mem_singleton]
      intro same
      have eq : S i = S j := by
        ext p
        rw [← single i p,← single j p,same]
      have lim := thin i j ne
      rw [← eq,Finset.inter_self] at lim
      omega
    all_goals simp [light,a,b]
  have apart : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint pay := by
    intro i _ j _ ne
    change Disjoint (pay i) (pay j)
    by_cases a : Disjoint (S i) Y <;> by_cases b : Disjoint (S j) Y
    · simpa [pay,a,b] using separateHH i j ne a b
    · simpa [pay,a,b] using separateHL i j a b
    · simpa [pay,a,b] using (separateHL j i b a).symm
    · simpa [pay,a,b] using separateLL i j ne
  have cover : Finset.univ.biUnion pay ⊆ pool := by
    intro w hw
    obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp hw
    by_cases d : Disjoint (S i) Y
    · exact Finset.mem_Ico.mpr (data i w (by simpa [pay,d] using wi)).1
    by_cases b : 2 ≤ (S i).card
    · have eq : w = o i := by simpa [pay,d,light,b] using wi
      exact eq ▸ isgate i b
    · simp [pay,d,light,b] at wi

  have outsideR : Disjoint (Finset.univ.biUnion pay) (reserve C Y) := by
    apply Finset.disjoint_left.mpr
    intro w hw wr
    obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp hw
    have many := (Finset.mem_filter.mp wr).2
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (losses C Y w).card)
    have hbase := (Finset.mem_filter.mp hp).2.1
    by_cases di : Disjoint (S i) Y
    · have hs := (data i w (by simpa [pay,di] using wi)).2.1
      obtain ⟨q,qi,qy⟩ := hs (mask Y) (fun _ h => decide_eq_true h) hbase
      exact Finset.disjoint_left.mp di qi (of_decide_eq_true qy)
    by_cases big : 2 ≤ (S i).card
    · have ow : w = o i := by simpa [pay,di,light,big] using wi
      subst w
      obtain ⟨q,qi,qy⟩ := Finset.not_disjoint_iff.mp di
      have sub : losses C Y (o i) ⊆ {q} := by
        intro r hr
        apply Finset.mem_singleton.mpr
        by_contra ne
        have no := (Finset.mem_filter.mp hr).2.2
        have qlive : mask (Y.erase r) q = true := decide_eq_true (Finset.mem_erase.mpr ⟨Ne.symm ne,qy⟩)
        have yes := (out i (mask (Y.erase r))).trans (decide_eq_true ⟨q,qi,qlive⟩)
        exact Bool.noConfusion (yes.symm.trans no)
      have small := Finset.card_le_card sub
      simp at small
      omega
    · simp [pay,di,light,big] at wi
  have bothsub : Finset.univ.biUnion pay ∪ reserve C Y ⊆ pool :=
    Finset.union_subset cover (Finset.filter_subset _ _)
  have each (i) : (if Disjoint (S i) Y then (S i).card else min 2 (S i).card) ≤ (pay i).card+1 := by
    by_cases di : Disjoint (S i) Y
    · simp only [pay,di,ite_true]
      apply card_le C Y (S i) t ops unique off (o i) di.symm
      · intro x _ hx
        exact of_decide_eq_true ((out i x).symm.trans hx)
      · intro p hp
        exact (out i _).trans (decide_eq_true ⟨p,hp,by simp⟩)
    by_cases big : 2 ≤ (S i).card <;> simp [pay,di,light,big] <;> omega
  have total := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => each i)
  rw [Finset.sum_add_distrib,← Finset.card_biUnion apart] at total
  have cap := Finset.card_le_card bothsub
  rw [Finset.card_union_of_disjoint outsideR] at cap
  simp [pool,Circuit.size] at cap
  have total' : (∑ i, if Disjoint (S i) Y then (S i).card else min 2 (S i).card) ≤
      (Finset.univ.biUnion pay).card + m := by simpa using total
  omega


theorem flag_source {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (nonempty : Y.Nonempty)
    (off : value C (mask Y) (n+t) = false)
    (minus : ∀ p ∈ Y, value C (mask (Y.erase p)) (n+t) = true) :
    ∃ target, value C (mask Y) target = true ∧
      ∀ p ∈ Y, value C (mask (Y.erase p)) target = false := by
  classical
  obtain ⟨p,py⟩ := nonempty
  have before (w) (hw : w < n+t) :
      value C (mask (Y.erase p)) w = true → value C (mask Y) w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w<n
      · let r : Fin n := ⟨w,raw⟩
        change value C _ r.val = true → value C _ r.val = true
        simp only [input_value,mask,decide_eq_true_eq,Finset.mem_erase]
        exact And.right
      by_cases hg : w<n+C.size
      · have idx : w-n<C.gates.length := by change w<n+C.gates.length at hg; omega
        obtain ⟨op,arity⟩ := ops C.gates[w-n] (List.getElem_mem idx)
        have ao : C.gates[w-n].op=GateOp.and ∨ C.gates[w-n].op=GateOp.or := by
          rcases op with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have eq := unique ⟨w-n,idx⟩ h
            change w-n=t at eq
            omega
        obtain ⟨P,_,earlier,step⟩ := gate_inputs C w (by omega) hg ao arity
        exact step _ _ fun r hr => ih r (earlier r hr) (lt_trans (earlier r hr) hw)
      · simp [missing_value C _ w (by omega : n+C.size≤w)]
  have small := minus p py
  have valid : n+t<n+C.size := by
    by_contra! h
    rw [missing_value C _ _ h] at small
    contradiction
  have idx : t<C.gates.length := by change n+t<n+C.gates.length at valid; omega
  obtain ⟨op,arity⟩ := ops C.gates[t] (List.getElem_mem idx)
  have isnot : C.gates[t].op = GateOp.not := by
    by_contra bad
    have ao : C.gates[t].op=GateOp.and ∨ C.gates[t].op=GateOp.or :=
      op.elim Or.inl (fun h => Or.inr (h.resolve_right bad))
    have parents := gate_inputs C (n+t) (by omega) valid
    simp only [Nat.add_sub_cancel_left] at parents
    obtain ⟨P,_,earlier,step⟩ := parents ao arity
    have yes := step _ _ (fun r hr => before r (earlier r hr)) small
    rw [off] at yes
    contradiction
  have evalAt (x : Fin n → Bool) := gate_value C x (n+t) (by omega) valid
  simp only [Nat.add_sub_cancel_left,isnot] at evalAt
  cases shape : C.gates[t].inputs with
  | nil =>
    have eq := evalAt (mask Y)
    simp [shape,GateOp.eval,off] at eq
  | cons target rest =>
    have eq := evalAt (mask Y)
    rw [off] at eq
    simp [shape,GateOp.eval] at eq
    have lt : target<n+t := by by_contra h; simp [h] at eq
    refine ⟨target,?_,?_⟩
    · cases hval : value C (mask Y) target
      · simp [lt,hval] at eq
      · rfl
    · intro q qy
      have test := evalAt (mask (Y.erase q))
      rw [minus q qy] at test
      cases hval : value C (mask (Y.erase q)) target
      · rfl
      · simp [shape,GateOp.eval,lt,hval] at test

theorem slack {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (off : value C (mask Y) (n+t) = false)
    (minus : ∀ p ∈ Y, value C (mask (Y.erase p)) (n+t) = true) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min 2 (S i).card) + (Y.card-1) ≤ C.gates.length+m := by
  have b := bound S C o t Y thin ops unique out off
  have r : Y.card ≤ (reserve C Y).card + 1 := by
    by_cases empty : Y.Nonempty
    · obtain ⟨g,yes,no⟩ := flag_source C Y t ops unique empty off minus
      exact sensitivity_count C Y t ops unique off g yes no
    · have e := Finset.not_nonempty_iff_eq_empty.mp empty
      simp [e]
  omega


/-- The full posted left side holds whenever the light excess fits the
reserve supplied by the sensitivity of the unique negated input. -/
theorem covered {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (t : ℕ) (Y : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (small : ∀ x : Fin n → Bool, (Finset.univ.filter (fun v => x v = true)).card < Y.card →
      value C x (n+t) = true)
    (off : value C (mask Y) (n+t) = false)
    (room : (∑ i, if Disjoint (S i) Y then 0 else min Y.card (S i).card - min 2 (S i).card) ≤ Y.card-1) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ C.gates.length+m := by
  classical
  have delete (p) (py : p ∈ Y) : value C (mask (Y.erase p)) (n+t) = true := by
    apply small
    have eq : Finset.univ.filter (fun v => mask (Y.erase p) v = true) = Y.erase p := by
      ext v; simp [mask]
    rw [eq]
    exact Finset.card_erase_lt_of_mem py
  have h := slack S C o t Y thin ops unique out off delete
  have each (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      (if Disjoint (S i) Y then (S i).card else min 2 (S i).card) +
      (if Disjoint (S i) Y then 0 else min Y.card (S i).card - min 2 (S i).card) := by
    by_cases dis : Disjoint (S i) Y <;> simp [dis] <;> omega
  have both := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => each i)
  rw [Finset.sum_add_distrib] at both
  omega

end WindowHeavyReserve
