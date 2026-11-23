import Research.CoverOr
import Research.ExcessOr

namespace PlaneResearch.PlaneOrderThree

open PEqualNP.CircuitLowerBounds PlaneResearch.ConeSemantics PlaneResearch.CoverCone
open PlaneResearch.TripleSystems (wiresFrom getD_wiresFrom_gate)

def lines (i : Fin 13) : Finset (Fin 13) := ({0,1,3,9} : Finset (Fin 13)).image (fun p => p+i)

private lemma thin : ∀ i j : Fin 13, i ≠ j → (lines i ∩ lines j).card ≤ 1 := by decide +kernel
private lemma fullCost : (∑ i, ((lines i).card-1)) = 39 := by decide +kernel
private lemma cost12 : ∀ a : Fin 13, (∑ i, ((lines i ∩ Finset.univ.erase a).card-1)) = 35 := by decide +kernel
private lemma cover3 : ∀ a b c : Fin 13, (lines a ∪ (lines b ∪ lines c)).card ≤ 10 := by decide +kernel

private lemma need_four_of_eleven (P : Finset (Fin 13)) (many : 11 ≤ P.card) (I : Finset (Fin 13)) (incl : P ⊆ I.biUnion lines) :
    4 ≤ I.card := by
  by_contra! small
  obtain ⟨J,sub,_,size⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ I)
    (by omega : I.card ≤ 3) (by decide)
  obtain ⟨x,y,z,_,_,_,eq⟩ := Finset.card_eq_three.mp size
  have s : P ⊆ J.biUnion lines :=
    incl.trans (Finset.biUnion_subset_biUnion_of_subset_left lines sub)
  rw [eq] at s
  have c := Finset.card_le_card s
  simp only [Finset.biUnion_insert,Finset.singleton_biUnion] at c
  have h := cover3 x y z
  omega

private lemma need_four (a : Fin 13) (I : Finset (Fin 13)) (incl : Finset.univ.erase a ⊆ I.biUnion lines) :
    4 ≤ I.card := need_four_of_eleven _ (by simp) I incl

/-- A unique NOT true on exactly one of the 13 singletons already requires 39 gates. -/
theorem one_singleton_cost (C : Circuit) (out : Fin 13 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 13 → Bool), val C (out i) x = true ↔ ∃ p ∈ lines i, x p = true)
    (t : Fin C.gates.length) (nt : (C.gates.get t).op = .not)
    (unique : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k=t)
    (a : Fin 13) (one : ∀ p : Fin 13, val C (13+t.val) (unitInput p) = decide (p=a)) : 39 ≤ C.size := by
  classical
  let A := Finset.univ.erase a
  have silent (p : Fin 13) (hp : p ∈ A) (k : Fin C.gates.length) (nk : (C.gates.get k).op = .not) :
      val C (13+k.val) (unitInput p) = false := by
    rw [unique k nk,one]
    exact decide_eq_false (Finset.mem_erase.mp hp).1
  have ground (p : Fin 13) (_ : p ∈ A) : ∃ i, p ∈ lines i :=
    ⟨p,Finset.mem_image.mpr ⟨0,by decide,by simp⟩⟩
  obtain ⟨b,ne⟩ := (by decide : ∀ a : Fin 13, ∃ b, b ≠ a) a
  have offN : val C (13+t.val) (unitInput b) = false := by simpa [one,ne]
  let g := C.gates.get t
  have gateeq (x : Fin 13 → Bool) : val C (13+t.val) x =
      g.op.eval (g.inputs.map (fun i => if i < 13+t.val then val C i x else false)) := by
    unfold val
    simpa only [g,List.get_eq_getElem,List.length_ofFn] using getD_wiresFrom_gate C.gates (List.ofFn x) t t.isLt
  have gn : g.op = .not := nt
  cases ins : g.inputs with
  | nil =>
    simp [gateeq,gn,ins,GateOp.eval] at offN
  | cons j js =>
    by_cases valid : j < 13+t.val
    · let root : Fin (13+C.gates.length) := ⟨j,by have := t.isLt; omega⟩
      have flip (p : Fin 13) : (!(val C root.val (unitInput p))) = decide (p=a) := by
        have e : val C (13+t.val) (unitInput p) = !(val C root.val (unitInput p)) := by
          rw [gateeq]
          simp [gn,ins,GateOp.eval,valid,root]
        exact e.symm.trans (one p)
      have fa : val C root.val (unitInput a) = false := by
        have h := flip a
        simpa using h
      have fill : marks A (unitInput a) unitInput (val C root.val) = A := by
        ext p
        simp only [marks,Finset.mem_filter]
        refine ⟨And.left,fun hp => ⟨hp,fa,?_⟩⟩
        have ne := (Finset.mem_erase.mp hp).1
        have q := flip p
        simpa [ne] using q
      have bound := singleton_cover_bound lines A (unitInput a) 0 ground thin C out hf hc t nt silent root fill 4 (need_four a)
      simpa only [A,cost12] using bound
    · simp [gateeq,gn,ins,GateOp.eval,valid] at offN

/-- Necessary condition for the exact 38-gate search on the incidence matrix in L-meta-957. -/
theorem two_singletons (C : Circuit) (out : Fin 13 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 13 → Bool), val C (out i) x = true ↔ ∃ p ∈ lines i, x p = true)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i=j)
    (small : C.size ≤ 38) :
    ∃ t : Fin C.gates.length, (C.gates.get t).op = .not ∧ ∃ a b : Fin 13, a ≠ b ∧
      val C (13+t.val) (unitInput a) = true ∧ val C (13+t.val) (unitInput b) = true := by
  classical
  have existsN : ∃ t : Fin C.gates.length, (C.gates.get t).op = .not := by
    by_contra none
    have h := monotone_linear_rows lines thin C out hf (fun k hk => none ⟨k,hk⟩) hc
    rw [fullCost] at h
    omega
  obtain ⟨t,nt⟩ := existsN
  refine ⟨t,nt,?_⟩
  have found : ∃ a : Fin 13, val C (13+t.val) (unitInput a) = true := by
    by_contra! empty
    have clean (i : Fin 13) (p : Fin 13) (_ : p ∈ lines i) (k : Fin C.gates.length)
        (nk : (C.gates.get k).op = .not) : val C (13+k.val) (unitInput p) = false := by
      rw [unique k t nk nt]
      simpa using empty p
    have h := (screen_rows lines lines (fun _ => Finset.Subset.rfl) thin C out hf hc
      (fun i => Or.inr (clean i))).trans (ordinaryCount_le C)
    rw [fullCost] at h
    omega
  obtain ⟨a,ha⟩ := found
  by_contra no
  have one (p : Fin 13) : val C (13+t.val) (unitInput p) = decide (p=a) := by
    by_cases same : p=a
    · simpa [same] using ha
    · simp only [decide_eq_false same]
      apply Bool.eq_false_iff.mpr
      intro h
      exact no ⟨p,a,same,h,ha⟩
  have lower := one_singleton_cost C out hf hc t nt (fun k nk => unique k t nk nt) a one
  omega

/-- A unique NOT true on exactly two singletons also requires at least 39 gates. -/
theorem two_singleton_cost (C : Circuit) (out : Fin 13 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 13 → Bool), val C (out i) x = true ↔ ∃ p ∈ lines i, x p = true)
    (t : Fin C.gates.length) (nt : (C.gates.get t).op = .not)
    (unique : ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k=t)
    (a b : Fin 13) (neab : a ≠ b) (one : ∀ p : Fin 13, val C (13+t.val) (unitInput p) = decide (p=a ∨ p=b)) : 39 ≤ C.size := by
  classical
  let A := (Finset.univ.erase a).erase b
  have silent (p : Fin 13) (hp : p ∈ A) (k : Fin C.gates.length) (nk : (C.gates.get k).op = .not) :
      val C (13+k.val) (unitInput p) = false := by
    rw [unique k nk,one]
    apply decide_eq_false
    obtain ⟨nb,mem⟩ := Finset.mem_erase.mp hp
    exact not_or_intro (Finset.mem_erase.mp mem).1 nb
  have ground (p : Fin 13) (_ : p ∈ A) : ∃ i, p ∈ lines i :=
    ⟨p,Finset.mem_image.mpr ⟨0,by decide,by simp⟩⟩
  obtain ⟨d,hda,hdb⟩ := (by decide : ∀ a b : Fin 13, ∃ d, d ≠ a ∧ d ≠ b) a b
  have offN : val C (13+t.val) (unitInput d) = false := by simp [one,hda,hdb]
  let g := C.gates.get t
  have gateeq (x : Fin 13 → Bool) : val C (13+t.val) x =
      g.op.eval (g.inputs.map (fun i => if i < 13+t.val then val C i x else false)) := by
    unfold val
    simpa only [g,List.get_eq_getElem,List.length_ofFn] using getD_wiresFrom_gate C.gates (List.ofFn x) t t.isLt
  have gn : g.op = .not := nt
  cases ins : g.inputs with
  | nil =>
    simp [gateeq,gn,ins,GateOp.eval] at offN
  | cons j js =>
    by_cases valid : j < 13+t.val
    · let root : Fin (13+C.gates.length) := ⟨j,by have := t.isLt; omega⟩
      have flip (p : Fin 13) : (!(val C root.val (unitInput p))) = decide (p=a ∨ p=b) := by
        have e : val C (13+t.val) (unitInput p) = !(val C root.val (unitInput p)) := by
          rw [gateeq]
          simp [gn,ins,GateOp.eval,valid,root]
        exact e.symm.trans (one p)
      have fa : val C root.val (unitInput a) = false := by
        have h := flip a
        simpa using h
      have fill : marks A (unitInput a) unitInput (val C root.val) = A := by
        ext p
        simp only [marks,Finset.mem_filter]
        refine ⟨And.left,fun hp => ⟨hp,fa,?_⟩⟩
        obtain ⟨nb,mem⟩ := Finset.mem_erase.mp hp
        have na := (Finset.mem_erase.mp mem).1
        have q := flip p
        simpa [na,nb] using q
      have eleven : 11 ≤ A.card :=
        (by decide +kernel : ∀ i j : Fin 13, i ≠ j → 11 ≤ ((Finset.univ.erase i).erase j).card) a b neab
      have cost : (∑ i, ((lines i ∩ insert a A).card-1)) = 35 :=
        (by decide +kernel : ∀ i j : Fin 13, i ≠ j →
          (∑ l, ((lines l ∩ insert i ((Finset.univ.erase i).erase j)).card-1)) = 35) a b neab
      have bound := anchor_cover_bound lines A a (unitInput a) 0 ground thin C out hf hc t nt silent
        root fill 4 (need_four_of_eleven A eleven)
      rw [cost] at bound
      exact bound
    · simp [gateeq,gn,ins,GateOp.eval,valid] at offN


/-- In the hypothetical 38-gate circuit the negation is true on at least three singletons. -/
theorem three_singletons (C : Circuit) (out : Fin 13 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 13 → Bool), val C (out i) x = true ↔ ∃ p ∈ lines i, x p = true)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i=j)
    (small : C.size ≤ 38) :
    ∃ t : Fin C.gates.length, (C.gates.get t).op = .not ∧ ∃ a b c : Fin 13,
      a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ val C (13+t.val) (unitInput a) = true ∧
      val C (13+t.val) (unitInput b) = true ∧ val C (13+t.val) (unitInput c) = true := by
  obtain ⟨t,nt,a,b,ne,ha,hb⟩ := two_singletons C out hf hc unique small
  refine ⟨t,nt,a,b,?_⟩
  by_contra no
  have one (p : Fin 13) : val C (13+t.val) (unitInput p) = decide (p=a ∨ p=b) := by
    by_cases pa : p=a
    · simpa [pa] using ha
    by_cases pb : p=b
    · simpa [pb] using hb
    · simp only [pa,pb,or_self,decide_false]
      apply Bool.eq_false_iff.mpr
      exact fun onP => no ⟨p,ne,pa,pb,ha,hb,onP⟩
  have h := two_singleton_cost C out hf hc t nt (fun k nk => unique k t nk nt) a b ne one
  omega

end PlaneResearch.PlaneOrderThree

namespace PlaneResearch.PlaneOrderThree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection

/-- The complete order-three plane needs at least 28 gates even if there are arbitrarily
many NOT gates. We fix two points to zero and apply the unrestricted excess bound. -/
theorem twenty_eight (C : Circuit) (out : Fin 13 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (lines i) x) :
    28 ≤ C.size := by
  let U : Finset (Fin 13) := {11,12}
  let R (i : Fin 13) := lines i \ U
  have touch : ∀ p ∈ U, ∃ i, p ∈ lines i := by decide +kernel
  have two : ∀ i, 2 ≤ (R i).card := by decide +kernel
  have sparse : ∀ i j, i ≠ j → (R i ∩ R j).card ≤ 1 := by decide +kernel
  have non (i) : (lines i \ U).Nonempty := Finset.card_pos.mp (by have := two i; change 0 < (R i).card; omega)
  obtain ⟨gs,o,sz,ok,ec⟩ := project_or_rows U lines touch non C.gates out hf hc
  let D := Circuit.mk gs 0
  have e (i) (x) : (Circuit.mk D.gates (o i)).eval (List.ofFn x) = sumRow (R i) x := ec i x
  have h := rank_excess R two sparse D o ok e
  have cost : (∑ i, ((R i).card-1)) = 31 := by decide +kernel
  have sur : (∑ i, ((R i).card-3)) = 6 := by decide +kernel
  have del : U.card = 2 := by decide +kernel
  rw [cost,sur] at h
  rw [del] at sz
  change 31 ≤ gs.length + (6-1) at h
  change 28 ≤ C.gates.length
  omega

end PlaneResearch.PlaneOrderThree
