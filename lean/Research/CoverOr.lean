import Research.MeasuredOr

namespace PlaneResearch.CoverCone

/-- A root's probe labels can be covered by one more region than the number of
nodes whose own probe labels fit in no single region. -/
theorem cover_bound {n m w : ℕ} (S : Fin w → Finset (Fin n)) (L : Fin m → Finset (Fin n))
    (parents : Fin w → Finset (Fin w)) (arity : ∀ j, (parents j).card ≤ 2)
    (earlier : ∀ j p, p ∈ parents j → p.val < j.val)
    (cover : ∀ j, (¬ ∃ l, S j ⊆ L l) → S j ⊆ (parents j).biUnion S)
    (root : Fin w) :
    ∃ lines : Finset (Fin m), S root ⊆ lines.biUnion L ∧ lines.card ≤
      (Finset.univ.filter (fun j => ¬ ∃ l, S j ⊆ L l)).card + 1 := by
  classical
  let step (u v : Fin w) := (¬ ∃ l, S u ⊆ L l) ∧ v ∈ parents u
  let live := Finset.univ.filter (Relation.ReflTransGen step root)
  let inner := live.filter (fun j => (¬ ∃ l, S j ⊆ L l))
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
    by_cases big : (¬ ∃ l, S j ⊆ L l)
    · obtain ⟨k,hk,hp'⟩ := Finset.mem_biUnion.mp (cover j big hp)
      have hlt := earlier j k hk
      exact ih k hlt (isLive.mpr ((isLive.mp hj).tail ⟨big,hk⟩)) hp'
    · apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_sdiff.mpr ⟨hj,fun h => big (Finset.mem_filter.mp h).2⟩, hp⟩

  have leaf (j : ↥leaves) : ∃ l, S j.val ⊆ L l := by
    by_contra none
    obtain ⟨v,h⟩ := Finset.mem_sdiff.mp j.property
    exact h (Finset.mem_filter.mpr ⟨v,none⟩)
  choose label subset using leaf
  let chosen := Finset.univ.image label
  refine ⟨chosen,?_,?_⟩
  · intro p hp
    obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp (paths root (isLive.mpr .refl) hp)
    exact Finset.mem_biUnion.mpr
      ⟨label ⟨j,hj⟩,Finset.mem_image.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,rfl⟩,subset ⟨j,hj⟩ hp⟩
  · have sub : inner ⊆ live := Finset.filter_subset ..
    have split : leaves.card + inner.card = live.card := Finset.card_sdiff_add_card_eq_card sub
    have small : chosen.card ≤ leaves.card := by
      simpa [chosen] using (Finset.card_image_le (s:=Finset.univ) (f:=label))
    have t : inner ⊆ Finset.univ.filter (fun j => ¬ ∃ l, S j ⊆ L l) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have total := Finset.card_le_card t
    omega

end PlaneResearch.CoverCone

namespace PlaneResearch.CoverCone
open PEqualNP.CircuitLowerBounds PlaneResearch.ConeSemantics
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_lt getD_wiresFrom_gate)
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

theorem circuit_cover {n d m : ℕ} (L : Fin m → Finset (Fin d)) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (T : Finset (Fin d)) (base : Fin n → Bool) (probe : Fin d → Fin n → Bool)
    (raw : ∀ k : Fin n, ∃ l, marks T base probe (fun x => x k) ⊆ L l)
    (neg : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      ∃ l, marks T base probe (val C (n+k.val)) ⊆ L l)
    (root : Fin (n+C.gates.length)) :
    ∃ lines : Finset (Fin m), marks T base probe (val C root.val) ⊆ lines.biUnion L ∧ lines.card ≤
      (Finset.univ.filter (fun j : Fin (n+C.gates.length) =>
        ¬ ∃ l, marks T base probe (val C j.val) ⊆ L l)).card + 1 := by
  classical
  let S (j : Fin (n+C.gates.length)) := marks T base probe (val C j.val)
  let P (j : Fin (n+C.gates.length)) := if low : j.val < n then ∅ else
    sources j (C.gates[j.val-n]'(by have := j.isLt; omega)).inputs
  apply PlaneResearch.CoverCone.cover_bound S L P _ _ _ root
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
      exact (big (by change ∃ l, marks T base probe (val C j.val) ⊆ L l; rw [eq]; exact raw ⟨_,lo⟩)).elim
    · let k : Fin C.gates.length := ⟨j.val-n,by have := j.isLt; omega⟩
      have idj : n+k.val=j.val := by dsimp [k]; omega
      let g := C.gates.get k
      have ok := (hf g (List.getElem_mem k.isLt)).1
      rcases ok with ha|ha|hn
      all_goals try
        exact (big (by change ∃ l, marks T base probe (val C j.val) ⊆ L l; rw [←idj]; exact neg k hn)).elim
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


end PlaneResearch.CoverCone

namespace PlaneResearch.CoverCone

open PEqualNP.CircuitLowerBounds PlaneResearch.ConeSemantics
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_lt)

/-- If every NOT is false on the tested singletons, an additional wire accepting
all of them pays for the number of target rows needed to cover them. -/
theorem probed_cover_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (base : Fin n → Bool)
    (line0 : Fin m) (ground : ∀ p ∈ A, ∃ i, p ∈ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (t : Fin C.gates.length) (nt : (C.gates.get t).op = .not)
    (silent : ∀ p ∈ A, ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      val C (n+k.val) (unitInput p) = false)
    (T : Fin m → Finset (Fin n)) (subset : ∀ i, T i ⊆ S i)
    (locally : ∀ i (k : Fin C.gates.length), (C.gates.get k).op = .not →
      (measured C (S i) (T i) (n+k.val)).card ≤ 1)
    (order : ∀ i j, i ≠ j → orderedNeg C (T i) (S j) ∨ orderedNeg C (T j) (S i))
    (root : Fin (n+C.gates.length))
    (fills : marks A base unitInput (val C root.val) = A) (K : ℕ)
    (need : ∀ I : Finset (Fin m), A ⊆ I.biUnion S → K ≤ I.card) :
    (∑ i, ((T i).card-1)) + K ≤ C.size := by
  classical
  let W (w : ℕ) := marks A base unitInput (val C w)
  let wide := Finset.univ.filter (fun k : Fin C.gates.length => ¬ ∃ i, W (n+k.val) ⊆ S i)
  let allWide := Finset.univ.filter (fun w : Fin (n+C.gates.length) => ¬ ∃ i, W w.val ⊆ S i)
  have raw (k : Fin n) : ∃ i, marks A base unitInput (fun x => x k) ⊆ S i := by
    by_cases member : k ∈ A
    · obtain ⟨i,hi⟩ := ground k member
      refine ⟨i,fun p hp => ?_⟩
      exact (of_decide_eq_true (Finset.mem_filter.mp hp).2.2 : k=p) ▸ hi
    · refine ⟨line0,fun p hp => ?_⟩
      have e : k=p := of_decide_eq_true (Finset.mem_filter.mp hp).2.2
      exact (member (e ▸ (Finset.mem_filter.mp hp).1)).elim
  have negEmpty (k : Fin C.gates.length) (hn : (C.gates.get k).op = .not) : W (n+k.val) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨pa,_,on'⟩ := Finset.mem_filter.mp hp
    change val C (n+k.val) (unitInput p) = true at on'
    simp [silent p pa k hn] at on'
  have neg (k : Fin C.gates.length) (hn : (C.gates.get k).op = .not) :
      ∃ i, W (n+k.val) ⊆ S i := ⟨line0,by rw [negEmpty k hn]; exact Finset.empty_subset _⟩
  obtain ⟨labels,incl,num⟩ := circuit_cover S C hf A base unitInput raw neg root
  rw [fills] at incl
  have count : K ≤ allWide.card+1 := (need _ incl).trans num
  have lower (w : Fin (n+C.gates.length)) (mem : w ∈ allWide) : n ≤ w.val := by
    by_contra! small
    have eq : @val n C w.val = fun x => x ⟨w.val,small⟩ := by
      funext x
      unfold val
      rw [getD_wiresFrom_lt _ _ _ (by simpa),List.getD_eq_getElem _ _ (by simpa using small),List.getElem_ofFn]
    have notSmall := (Finset.mem_filter.mp mem).2
    apply notSmall
    dsimp [W]
    rw [eq]
    exact raw _
  let idx (w : ↥allWide) : Fin C.gates.length :=
    ⟨w.val.val-n,by have := lower w.val w.property; have := w.val.isLt; omega⟩
  have idw (w : ↥allWide) : n+(idx w).val=w.val.val := by
    dsimp [idx]; have := lower w.val w.property; omega
  let lift (w : ↥allWide) : ↥wide :=
    ⟨idx w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, idw w ▸ (Finset.mem_filter.mp w.property).2⟩⟩
  have inject : Function.Injective lift := by
    intro a b eq
    have same : idx a = idx b := congrArg Subtype.val eq
    apply Subtype.ext
    apply Fin.ext
    rw [←idw a,←idw b,same]
  have wc : allWide.card ≤ wide.card := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift inject
  let available := (Finset.univ.erase t) \ wide
  have allow (i) (k : Fin C.gates.length) (big : 1 < (measured C (S i) (T i) (n+k.val)).card) :
      k ∈ available := by
    have kt : k ≠ t := by rintro rfl; exact (Nat.not_lt_of_ge (locally i k nt)) big
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨kt,Finset.mem_univ _⟩,?_⟩
    intro belongs
    apply (Finset.mem_filter.mp belongs).2
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt big)
    have off := (Finset.mem_filter.mp ha).2.1
    refine ⟨i,fun p hp => ?_⟩
    by_contra missing
    obtain ⟨pa,_,on'⟩ := Finset.mem_filter.mp hp
    have xy (b : Fin n) (h : unitInput p b = true) : exterior (S i) b = true := by
      have e : b=p := of_decide_eq_true h
      exact e ▸ decide_eq_true missing
    have orderN (q : Fin C.gates.length) (nq : (C.gates.get q).op = .not)
        (h : val C (n+q.val) (unitInput p) = true) : val C (n+q.val) (exterior (S i)) = true := by
      simp [silent p pa q nq] at h
    have onExt := compare C hf _ _ xy orderN (n+k.val) on'
    change val C (n+k.val) (exterior (S i)) = false at off
    simp [off] at onExt
  have rowCost := measured_lower_on S T subset thin C out hf hc locally
    order available allow
  have dis : Disjoint available wide := Finset.sdiff_disjoint
  have notWide : t ∉ wide := fun h => (Finset.mem_filter.mp h).2 (neg t nt)
  have ntu : t ∉ available ∪ wide := by simp [available,notWide]
  have bound : (insert t (available ∪ wide)).card ≤ C.gates.length := by
    simpa using (Finset.card_le_card (Finset.subset_univ (insert t (available ∪ wide))))
  rw [Finset.card_insert_of_notMem ntu,Finset.card_union_of_disjoint dis] at bound
  change (∑ i, ((T i).card-1)) + K ≤ C.gates.length
  omega

theorem singleton_cover_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (base : Fin n → Bool)
    (line0 : Fin m) (ground : ∀ p ∈ A, ∃ i, p ∈ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (t : Fin C.gates.length) (nt : (C.gates.get t).op = .not)
    (silent : ∀ p ∈ A, ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      val C (n+k.val) (unitInput p) = false)
    (root : Fin (n+C.gates.length))
    (fills : marks A base unitInput (val C root.val) = A) (K : ℕ)
    (need : ∀ I : Finset (Fin m), A ⊆ I.biUnion S → K ≤ I.card) :
    (∑ i, ((S i ∩ A).card-1)) + K ≤ C.size := by
  classical
  let T (i : Fin m) := S i ∩ A
  have locally (i) (k : Fin C.gates.length) (hn : (C.gates.get k).op = .not) :
      (measured C (S i) (T i) (n+k.val)).card ≤ 1 := by
    have empty : measured C (S i) (T i) (n+k.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨pt,_,on'⟩ := Finset.mem_filter.mp hp
      change val C (n+k.val) (unitInput p) = true at on'
      simp [silent p (Finset.mem_inter.mp pt).2 k hn] at on'
    simp [empty]
  have ord (i j : Fin m) : orderedNeg C (T i) (S j) := by
    intro p pt _ k hk on'
    simp [silent p (Finset.mem_inter.mp pt).2 k hk] at on'
  exact probed_cover_bound S A base line0 ground thin C out hf hc t nt silent T
    (fun _ => Finset.inter_subset_left) locally (fun i j _ => Or.inl (ord i j)) root fills K need

/-- Add one common exceptional singleton to the measured row probes. -/
theorem anchor_cover_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (A : Finset (Fin n))
    (a : Fin n) (base : Fin n → Bool)
    (line0 : Fin m) (ground : ∀ p ∈ A, ∃ i, p ∈ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin n → Bool), val C (out i) x = true ↔ ∃ p ∈ S i, x p = true)
    (t : Fin C.gates.length) (nt : (C.gates.get t).op = .not)
    (silent : ∀ p ∈ A, ∀ k : Fin C.gates.length, (C.gates.get k).op = .not →
      val C (n+k.val) (unitInput p) = false)
    (root : Fin (n+C.gates.length))
    (fills : marks A base unitInput (val C root.val) = A) (K : ℕ)
    (need : ∀ I : Finset (Fin m), A ⊆ I.biUnion S → K ≤ I.card) :
    (∑ i, ((S i ∩ insert a A).card-1)) + K ≤ C.size := by
  classical
  let T (i : Fin m) := S i ∩ insert a A
  have locally (i) (k : Fin C.gates.length) (hn : (C.gates.get k).op = .not) :
      (measured C (S i) (T i) (n+k.val)).card ≤ 1 := by
    have ss : measured C (S i) (T i) (n+k.val) ⊆ {a} := by
      intro p hp
      obtain ⟨pt,_,on'⟩ := Finset.mem_filter.mp hp
      change val C (n+k.val) (unitInput p) = true at on'
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp pt).2 with same | inA
      · simpa only [Finset.mem_singleton] using same
      · simp [silent p inA k hn] at on'
    simpa only [Finset.card_singleton] using Finset.card_le_card ss
  have directed (i j : Fin m) (good : a ∈ S i → a ∈ S j) : orderedNeg C (T i) (S j) := by
    intro p pt off k nt' on'
    rcases Finset.mem_insert.mp (Finset.mem_inter.mp pt).2 with same | member
    · subst p
      exact (off (good (Finset.mem_inter.mp pt).1)).elim
    · simp [silent p member k nt'] at on'
  apply probed_cover_bound S A base line0 ground thin C out hf hc t nt silent T
    (fun _ => Finset.inter_subset_left) locally _ root fills K need
  intro i j _
  by_cases member : a ∈ S j
  · exact Or.inl (directed i j (fun _ => member))
  · exact Or.inr (directed j i (fun h => (member h).elim))

end PlaneResearch.CoverCone
