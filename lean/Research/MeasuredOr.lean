import Research.UnrestrictedOr


namespace PlaneResearch.SupportCone

/-- A binary computation covering distinct labels from leaves of support at most one
requires at least one fewer nontrivial vertices than the number of labels at its root.
Supports can shrink, and a predecessor can be shared by arbitrarily many vertices. -/
theorem support_bound {n w : ℕ} (S : Fin w → Finset (Fin n))
    (parents : Fin w → Finset (Fin w)) (arity : ∀ j, (parents j).card ≤ 2)
    (earlier : ∀ j p, p ∈ parents j → p.val < j.val)
    (cover : ∀ j, 1 < (S j).card → S j ⊆ (parents j).biUnion S)
    (root : Fin w) :
    (S root).card ≤ (Finset.univ.filter (fun j => 1 < (S j).card)).card + 1 := by
  classical
  let step (u v : Fin w) := 1 < (S u).card ∧ v ∈ parents u
  let live := Finset.univ.filter (Relation.ReflTransGen step root)
  let inner := live.filter (fun j => 1 < (S j).card)
  let leaves := live \ inner
  have isLive {j : Fin w} : j ∈ live ↔ Relation.ReflTransGen step root j := by simp [live]
  have reached {j : Fin w} (hj : j ∈ live) : j = root ∨ j ∈ inner.biUnion parents := by
    rcases (isLive.mp hj).cases_tail with h|⟨p,hp,hs⟩
    · exact Or.inl (by first | exact h | exact h.symm)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨isLive.mpr hp,hs.1⟩,hs.2⟩)
  have union_bound : live.card ≤ 1 + inner.card*2 := by
    have sub : live ⊆ {root} ∪ inner.biUnion parents := by
      intro j hj
      exact Finset.mem_union.mpr ((reached hj).imp_left (fun h => Finset.mem_singleton.mpr h))
    have u := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
    have v : (inner.biUnion parents).card ≤ ∑ j ∈ inner, (parents j).card := Finset.card_biUnion_le
    have z := Finset.sum_le_sum (s:=inner) (fun j _ => arity j)
    simp only [Finset.card_singleton] at u
    simp at z
    omega
  have paths (j : Fin w) : j ∈ live → S j ⊆ leaves.biUnion S := by
    refine (inferInstance : WellFoundedLT (Fin w)).induction
      (motive := fun v => v ∈ live → S v ⊆ leaves.biUnion S) j ?_
    intro j ih hj p hp
    by_cases big : 1 < (S j).card
    · obtain ⟨k,hk,hp'⟩ := Finset.mem_biUnion.mp (cover j big hp)
      have hlt := earlier j k hk
      exact ih k hlt (isLive.mpr ((isLive.mp hj).tail ⟨big,hk⟩)) hp'
    · apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_sdiff.mpr ⟨hj,fun h => big (Finset.mem_filter.mp h).2⟩, hp⟩
  have r := Finset.card_le_card (paths root (isLive.mpr .refl))
  have u : (leaves.biUnion S).card ≤ ∑ j ∈ leaves, (S j).card := Finset.card_biUnion_le
  have low (j) (hj : j ∈ leaves) : (S j).card ≤ 1 := by
    by_contra! h
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hj
    exact h2 (Finset.mem_filter.mpr ⟨h1,h⟩)
  have l := Finset.sum_le_sum low
  simp at l
  have sub : inner ⊆ live := Finset.filter_subset ..
  have split : leaves.card + inner.card = live.card := Finset.card_sdiff_add_card_eq_card sub
  have t : inner ⊆ Finset.univ.filter (fun j => 1 < (S j).card) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have total := Finset.card_le_card t
  omega

end PlaneResearch.SupportCone

namespace PlaneResearch.ConeSemantics

open PEqualNP.CircuitLowerBounds
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_lt getD_wiresFrom_gate)

def val {n : ℕ} (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

/-- Labels for which a wire changes from false on the baseline to true on the probe. -/
def marks {n d : ℕ} (T : Finset (Fin d)) (base : Fin n → Bool) (probe : Fin d → Fin n → Bool)
    (f : (Fin n → Bool) → Bool) : Finset (Fin d) :=
  T.filter fun p => f base = false ∧ f (probe p) = true

private lemma inc {op : GateOp} (allowed : op = .and ∨ op = .or) (ins : List ℕ)
    (base probe : ℕ → Bool) (off : op.eval (ins.map base) = false)
    (on' : op.eval (ins.map probe) = true) : ∃ i ∈ ins, base i = false ∧ probe i = true := by
  rcases allowed with rfl|rfl
  · have allon : ∀ i ∈ ins, probe i = true := by
      simpa [GateOp.eval,List.all_eq_true] using on'
    by_contra! h
    have allbase : ∀ i ∈ ins, base i = true := by
      intro i hi
      cases e : base i with
      | false => exact ((h i hi e) (allon i hi)).elim
      | true => rfl
    have onbase : GateOp.and.eval (ins.map base) = true := by
      simpa [GateOp.eval,List.all_eq_true] using allbase
    simp_all
  · obtain ⟨i,hi,hu⟩ : ∃ i ∈ ins, probe i = true := by
      simpa [GateOp.eval,List.any_eq_true] using on'
    refine ⟨i,hi,?_,hu⟩
    apply Bool.eq_false_iff.mpr
    intro hb
    have check : GateOp.or.eval (ins.map base) = true := by
      simpa [GateOp.eval,List.any_eq_true] using (show ∃ j ∈ ins, base j = true from ⟨i,hi,hb⟩)
    simp_all

private def sources {w : ℕ} (j : Fin w) (ins : List ℕ) : Finset (Fin w) :=
  Finset.univ.filter fun v => v.val < j.val ∧ v.val ∈ ins

private lemma sources_card {w : ℕ} (j : Fin w) (ins : List ℕ) :
    (sources j ins).card ≤ ins.length := by
  apply le_trans _ ins.toFinset_card_le
  apply Finset.card_le_card_of_injOn Fin.val
  · intro x hx
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2.2
  · intro a _ b _ h
    exact Fin.ext h

theorem circuit_marks {n d : ℕ} (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (T : Finset (Fin d)) (base : Fin n → Bool) (probe : Fin d → Fin n → Bool)
    (raw : ∀ k : Fin n, (marks T base probe (fun x => x k)).card ≤ 1)
    (neg : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      (marks T base probe (val C (n+k.val))).card ≤ 1)
    (root : Fin (n+C.gates.length)) :
    (marks T base probe (val C root.val)).card ≤
      (Finset.univ.filter (fun j : Fin (n+C.gates.length) =>
        1 < (marks T base probe (val C j.val)).card)).card + 1 := by
  classical
  let S (j : Fin (n+C.gates.length)) := marks T base probe (val C j.val)
  let P (j : Fin (n+C.gates.length)) := if low : j.val < n then ∅ else
    sources j (C.gates[j.val-n]'(by have := j.isLt; omega)).inputs
  apply PlaneResearch.SupportCone.support_bound S P _ _ _ root
  · intro j
    unfold P
    split
    · simp
    · exact (sources_card ..).trans (hf _ (List.getElem_mem _)).2
  · intro j p hp
    unfold P at hp
    split at hp
    · simp at hp
    · exact (Finset.mem_filter.mp hp).2.1
  · intro j big
    by_cases lo : j.val < n
    · have eq : @val n C j.val = (fun x => x ⟨j.val,lo⟩) := by
        funext x
        unfold val
        rw [getD_wiresFrom_lt _ _ _ (by simpa)]
        rw [List.getD_eq_getElem _ _ (by simpa using lo),List.getElem_ofFn]
      exact ((Nat.not_lt_of_ge (raw ⟨_,lo⟩)) (eq ▸ big)).elim
    · let k : Fin C.gates.length := ⟨j.val-n,by have := j.isLt; omega⟩
      have idj : n+k.val=j.val := by dsimp [k]; omega
      let g := C.gates.get k
      have ok := (hf g (List.getElem_mem k.isLt)).1
      rcases ok with ha|ha|hn
      all_goals try
        exact ((Nat.not_lt_of_ge (neg k hn)) (idj ▸ big)).elim
      all_goals
        have gateeq (x : Fin n → Bool) : val C j.val x =
            g.op.eval (g.inputs.map (fun i => if i<j.val then val C i x else false)) := by
          unfold val
          simpa only [g,List.get_eq_getElem,List.length_ofFn,idj] using
            getD_wiresFrom_gate C.gates (List.ofFn x) k k.isLt
        intro p hp
        obtain ⟨hT,off,on'⟩ := Finset.mem_filter.mp hp
        change val C j.val base = false at off
        change val C j.val (probe p) = true at on'
        rw [gateeq] at off on'
        obtain ⟨i,hi,offi,oni⟩ := inc (by first | exact Or.inl ha | exact Or.inr ha) g.inputs _ _ off on'
        have hlt : i < j.val := by by_contra bad; simp [bad] at oni
        let v : Fin (n+C.gates.length) := ⟨i,lt_trans hlt j.isLt⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨v,?_, Finset.mem_filter.mpr ⟨hT,by simpa [hlt] using offi,by simpa [hlt] using oni⟩⟩
        simp only [P, dif_neg lo, sources, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt,hi⟩

end PlaneResearch.ConeSemantics

namespace PlaneResearch.ConeSemantics

open PEqualNP.CircuitLowerBounds
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_lt getD_wiresFrom_gate length_wiresFrom)

/-- Any decrease along comparable inputs must already occur at a negation gate. -/
theorem compare {n : ℕ} (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (x y : Fin n → Bool) (xy : ∀ i, x i = true → y i = true)
    (neg : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      val C (n+k.val) x = true → val C (n+k.val) y = true) :
    ∀ j : ℕ, val C j x = true → val C j y = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro on'
    by_cases raw : j < n
    · have input (z : Fin n → Bool) : val C j z = z ⟨j,raw⟩ := by
        unfold val
        rw [getD_wiresFrom_lt _ _ _ (by simpa)]
        rw [List.getD_eq_getElem _ _ (by simpa using raw),List.getElem_ofFn]
      rw [input] at on' ⊢
      exact xy _ on'
    by_cases inside : j < n+C.gates.length
    · let k : Fin C.gates.length := ⟨j-n,by omega⟩
      have idj : n+k.val=j := by dsimp [k]; omega
      let g := C.gates.get k
      by_cases isNeg : g.op = .not
      · exact idj ▸ neg k isNeg (idj ▸ on')
      have mono : g.op = .and ∨ g.op = .or := by
        rcases (hf g (List.getElem_mem k.isLt)).1 with h|h|h
        · exact Or.inl h
        · exact Or.inr h
        · exact (isNeg h).elim
      have gateeq (z : Fin n → Bool) : val C j z =
            g.op.eval (g.inputs.map (fun i => if i<j then val C i z else false)) := by
        unfold val
        simpa only [g,List.get_eq_getElem,List.length_ofFn,idj] using
          getD_wiresFrom_gate C.gates (List.ofFn z) k k.isLt
      apply Bool.eq_true_of_not_eq_false
      intro off
      rw [gateeq] at off on'
      obtain ⟨i,_,offi,oni⟩ := inc mono g.inputs _ _ off on'
      have lt : i<j := by by_contra bad; simp [bad] at oni
      have a : val C i x = true := by simpa [lt] using oni
      have b : val C i y = false := by simpa [lt] using offi
      simpa [b] using ih i lt a
    · unfold val at on'
      rw [List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)] at on'
      contradiction

end PlaneResearch.ConeSemantics

namespace PlaneResearch.ConeSemantics

open PEqualNP.CircuitLowerBounds
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_lt length_wiresFrom)

def unitInput {n : ℕ} (p : Fin n) : Fin n → Bool := fun k => decide (k=p)
def exterior {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun k => decide (k ∉ A)

def measured {n : ℕ} (C : Circuit) (A T : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  marks T (exterior A) unitInput (val C w)

def orderedNeg {n : ℕ} (C : Circuit) (probes outside : Finset (Fin n)) : Prop :=
  ∀ p ∈ probes, p ∉ outside → ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
    val C (n+k.val) (unitInput p) = true → val C (n+k.val) (exterior outside) = true

def ordinary (g : Gate) : Bool := match g.op with | .not => false | _ => true

def ordinaryCount (C : Circuit) :=
  (Finset.univ.filter fun k : Fin C.gates.length => ordinary (C.gates.get k)).card

theorem ordinaryCount_le (C : Circuit) : ordinaryCount C ≤ C.size := by
  simpa [ordinaryCount,Circuit.size] using Finset.card_filter_le
    (p:=fun k : Fin C.gates.length => ordinary (C.gates.get k) = true) Finset.univ

/-- A lower bound from one baseline and a set of singleton probes per row. Only
negation-gate values are needed to check directed comparisons between rows. -/
theorem measured_lower_on {n m : ℕ} (S T : Fin m → Finset (Fin n)) (subset : ∀ i, T i ⊆ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (localNeg : ∀ i (k : Fin C.gates.length), (C.gates.get k).op = .not →
      (measured C (S i) (T i) (n+k.val)).card ≤ 1)
    (order : ∀ i j, i ≠ j → orderedNeg C (T i) (S j) ∨ orderedNeg C (T j) (S i))
    (available : Finset (Fin C.gates.length))
    (availability : ∀ i (k : Fin C.gates.length), 1 < (measured C (S i) (T i) (n+k.val)).card →
      k ∈ available) : (∑ i, ((T i).card-1)) ≤ available.card := by
  classical
  let M (i : Fin m) (w : ℕ) := measured C (S i) (T i) w
  let pool (i : Fin m) := Finset.univ.filter (fun j : Fin (n+C.gates.length) => 1 < (M i j.val).card)
  have raw (i : Fin m) (k : Fin n) :
      (marks (T i) (exterior (S i)) unitInput (fun x => x k)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (of_decide_eq_true (Finset.mem_filter.mp ha).2.2).symm.trans
      (of_decide_eq_true (Finset.mem_filter.mp hb).2.2)
  have charge (i : Fin m) : (T i).card-1 ≤ (pool i).card := by
    by_cases ne : (T i).Nonempty
    · obtain ⟨p,hp⟩ := ne
      have on' := (hc i (unitInput p)).2 ⟨p,subset i hp,by simp [unitInput]⟩
      have valid : out i < n+C.gates.length := by
        by_contra! inv
        unfold val at on'
        rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using inv)] at on'
        contradiction
      have off : val C (out i) (exterior (S i)) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨q,hq,no⟩ := (hc i _).1 h
        exact (of_decide_eq_true no) hq
      have all : M i (out i) = T i := by
        ext q
        simp only [M,measured,marks,Finset.mem_filter]
        exact ⟨And.left,fun h => ⟨h,off,(hc i _).2 ⟨q,subset i h,by simp [unitInput]⟩⟩⟩
      have b := circuit_marks C hf (T i) (exterior (S i)) unitInput (raw i) (localNeg i) ⟨out i,valid⟩
      change (M i (out i)).card ≤ (pool i).card + 1 at b
      rw [all] at b
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp ne]
  have direction (i j : Fin m) (ne : i ≠ j) (ord : orderedNeg C (T i) (S j))
      (w : Fin (n+C.gates.length)) (wi : w ∈ pool i) (wj : w ∈ pool j) : False := by
    obtain ⟨a,ha,b,hb,diff⟩ := Finset.one_lt_card.mp (Finset.mem_filter.mp wi).2
    obtain ⟨t,ht⟩ := Finset.card_pos.mp (by have := (Finset.mem_filter.mp wj).2; omega :
      0 < (M j w.val).card)
    have off := (Finset.mem_filter.mp ht).2.1
    have membership (p : Fin n) (h : p ∈ M i w.val) : p ∈ S i ∩ S j := by
      obtain ⟨pt,_,on'⟩ := Finset.mem_filter.mp h
      refine Finset.mem_inter.mpr ⟨subset i pt,?_⟩
      by_contra bad
      have xy (k : Fin n) (v : unitInput p k = true) : exterior (S j) k = true := by
        have e : k=p := of_decide_eq_true v
        exact e ▸ decide_eq_true bad
      have yes := compare C hf (unitInput p) (exterior (S j)) xy (ord p pt bad) w.val on'
      change val C w.val (exterior (S j)) = false at off
      simp [off] at yes
    exact diff (Finset.card_le_one.mp (thin i j ne) _ (membership a ha) _ (membership b hb))
  have disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint pool := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro w wi wj
    exact (order i j ne).elim (fun d => direction i j ne d w wi wj)
      (fun d => direction j i ne.symm d w wj wi)
  let used := Finset.univ.biUnion pool
  have lower (w : Fin (n+C.gates.length)) (hw : w ∈ used) : n ≤ w.val := by
    obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp hw
    by_contra! small
    have e : @val n C w.val = fun x => x ⟨w.val,small⟩ := by
      funext x
      unfold val
      rw [getD_wiresFrom_lt _ _ _ (by simpa),List.getD_eq_getElem _ _ (by simpa using small),List.getElem_ofFn]
    have big := (Finset.mem_filter.mp h).2
    change 1 < (marks (T i) (exterior (S i)) unitInput (val C w.val)).card at big
    rw [e] at big
    exact (Nat.not_lt_of_ge (raw i ⟨_,small⟩)) big
  let refer (w : ↥used) : Fin C.gates.length :=
    ⟨w.val.val-n,by have := w.val.isLt; have := lower w.val w.property; omega⟩
  have key (w : ↥used) : n+(refer w).val=w.val.val := by
    dsimp [refer]
    have := lower w.val w.property
    omega
  have yes (w : ↥used) : refer w ∈ available := by
    obtain ⟨i,_,mem⟩ := Finset.mem_biUnion.mp w.property
    apply availability i (refer w)
    rw [key]
    exact (Finset.mem_filter.mp mem).2
  let lift (w : ↥used) : ↥available := ⟨refer w,yes w⟩
  have inj : Function.Injective lift := by
    intro a b e
    have same : refer a = refer b := congrArg Subtype.val e
    apply Subtype.ext
    apply Fin.ext
    rw [←key a,←key b,same]
  have budget : used.card ≤ available.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift inj
  have u : used.card = ∑ i, (pool i).card := Finset.card_biUnion disj
  rw [u] at budget
  exact (Finset.sum_le_sum (fun i _ => charge i)).trans budget

theorem measured_lower {n m : ℕ} (S T : Fin m → Finset (Fin n)) (subset : ∀ i, T i ⊆ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (localNeg : ∀ i (k : Fin C.gates.length), (C.gates.get k).op = .not →
      (measured C (S i) (T i) (n+k.val)).card ≤ 1)
    (order : ∀ i j, i ≠ j → orderedNeg C (T i) (S j) ∨ orderedNeg C (T j) (S i)) :
    (∑ i, ((T i).card-1)) ≤ ordinaryCount C := by
  apply measured_lower_on S T subset thin C out hf hc localNeg order _ ?_
  intro i k big
  have nonneg : (C.gates.get k).op ≠ .not := fun h => (Nat.not_lt_of_ge (localNeg i k h)) big
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  unfold ordinary
  cases h : (C.gates.get k).op <;> simp_all

theorem monotone_linear_rows {n m : ℕ} (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (positive : ∀ k : Fin C.gates.length, (C.gates.get k).op ≠ .not)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true) :
    (∑ i, ((S i).card-1)) ≤ C.size :=
  (measured_lower S S (fun _ => Finset.Subset.rfl) thin C out hf hc
    (fun _ k h => (positive k h).elim)
    (fun _ _ _ => Or.inl (fun _ _ _ k h => (positive k h).elim))).trans (ordinaryCount_le C)

theorem screen_rows {n m : ℕ} (S T : Fin m → Finset (Fin n)) (subset : ∀ i, T i ⊆ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (clean : ∀ i, (∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      val C (n+k.val) (exterior (S i)) = true) ∨
      (∀ p ∈ T i, ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
        val C (n+k.val) (unitInput p) = false)) : (∑ i, ((T i).card-1)) ≤ ordinaryCount C := by
  apply measured_lower S T subset thin C out hf hc
  · intro i k hn
    have empty : measured C (S i) (T i) (n+k.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p h
      obtain ⟨pt,off,on'⟩ := Finset.mem_filter.mp h
      rcases clean i with h|h
      · simp [h k hn] at off
      · simp [h p pt k hn] at on'
    simp [empty]
  · intro i j _
    rcases clean i with bi|si
    · exact Or.inr (fun _ _ _ k hk _ => bi k hk)
    · apply Or.inl
      intro p hp _ k hk h
      simp [si p hp k hk] at h

end PlaneResearch.ConeSemantics
