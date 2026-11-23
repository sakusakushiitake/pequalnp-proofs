import Research.ProjectedOr

namespace PlaneResearch.InputDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection

def firstVal {n : ℕ} (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)

lemma tail_eq {n : ℕ} (g : Gate) (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    (Circuit.mk gs o).eval (List.ofFn (Fin.snoc x (firstVal g x))) =
      (Circuit.mk (g::gs) o).eval (List.ofFn x) := by
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private def eraseBit {n : ℕ} (p : Fin n) (x : Fin n → Bool) := Function.update x p false

private lemma erased_sum {n : ℕ} (S : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool) :
    sumRow S (eraseBit p x) = sumRow (S.erase p) x := by
  simp only [sumRow,decide_eq_decide]
  constructor
  · rintro ⟨a,ha,on'⟩
    have ne : a ≠ p := by rintro rfl; simp [eraseBit] at on'
    exact ⟨a,Finset.mem_erase.mpr ⟨ne,ha⟩,by simpa [eraseBit,ne] using on'⟩
  · rintro ⟨a,ha,on'⟩
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
    exact ⟨a,mem,by simpa [eraseBit,ne] using on'⟩

private lemma sum_vary {n : ℕ} {S : Finset (Fin n)} (h : S.Nonempty) :
    sumRow S (fun _ => false) ≠ sumRow S (fun _ => true) := by
  simpa [sumRow,Finset.Nonempty] using h

private def pinned {n : ℕ} (p : Fin n) (d : Bool ⊕ Fin n) : Fin (n+1) → Bool ⊕ Fin n :=
  Fin.snoc (fun i => if i=p then .inl false else .inr i) d

private lemma assigned_pin {n : ℕ} (p : Fin n) (d : Bool ⊕ Fin n) (x : Fin n → Bool) :
    assignInput (pinned p d) x = Fin.snoc (eraseBit p x) (d.elim id x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [assignInput,pinned]
  · by_cases e : j=p <;> simp [assignInput,pinned,eraseBit,e]

/-- The first gate disappears after fixing p. A second gate disappears if a target
can distinguish two assignments differing only at the two pinned tail inputs. -/
private theorem erase_after_first {n r : ℕ} (S : Fin r → Finset (Fin n))
    (p : Fin n) (d : Bool ⊕ Fin n) (g : Gate) (gs : List Gate) (out : Fin r → ℕ)
    (hf : FanInTwo ⟨g::gs,0⟩)
    (hc : ∀ j x, (Circuit.mk (g::gs) (out j)).eval (List.ofFn x) = sumRow (S j) x)
    (non : ∀ j, ((S j).erase p).Nonempty)
    (bypass : ∀ x : Fin n → Bool, firstVal g (eraseBit p x) = d.elim id x) :
    ∃ (hs : List Gate) (o : Fin r → ℕ), hs.length+1 ≤ (g::gs).length ∧ FanInTwo ⟨hs,0⟩ ∧
      (∀ j x, (Circuit.mk hs (o j)).eval (List.ofFn x) = sumRow ((S j).erase p) x) ∧
      ((∃ (j : Fin r) (u v : Fin n → Bool), (∀ i, i ≠ p → u i = v i) ∧
        (∀ a, d = .inr a → firstVal g u = firstVal g v) ∧ sumRow (S j) u ≠ sumRow (S j) v) →
        hs.length+2 ≤ (g::gs).length) := by
  have ev (j : Fin r) (x : Fin n → Bool) : (Circuit.mk gs (out j)).eval
      (List.ofFn (assignInput (pinned p d) x)) = sumRow ((S j).erase p) x := by
    rw [assigned_pin,← bypass,tail_eq,hc,erased_sum]
  obtain ⟨hs,o,ok,weak,hev,less⟩ := specialize_outputs (pinned p d) gs out
    (fun a ha => hf a (List.mem_cons_of_mem _ ha))
    (fun j => ⟨fun _ => false,fun _ => true,by simp only [ev]; exact sum_vary (non j)⟩)
  refine ⟨hs,o,by simpa using weak,ok,fun j x => (hev j x).trans (ev j x),?_⟩
  intro dep
  have save : hs.length+1 ≤ gs.length := by
    apply less
    obtain ⟨j,u,v,away,last,diff⟩ := dep
    refine ⟨j,Fin.snoc u (firstVal g u),Fin.snoc v (firstVal g v),?_,?_⟩
    · intro i a
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa [pinned] using last a
      · by_cases eq : k=p <;> simp [pinned,eq,away] 
    · rwa [tail_eq,tail_eq,hc,hc]
  simpa only [List.length_cons] using Nat.succ_le_succ save

inductive HeadForm {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop where
  | flat (d : Bool ⊕ Fin n) (h : ∀ x, f x = d.elim id x)
  | neg (p : Fin n) (h : ∀ x, f x = !(x p))
  | conj (p q : Fin n) (ne : p ≠ q) (h : ∀ x, f x = (x p && x q))
  | disj (p q : Fin n) (ne : p ≠ q) (h : ∀ x, f x = (x p || x q))

private def raw {n : ℕ} (i : ℕ) : Bool ⊕ Fin n :=
  if h : i < n then .inr ⟨i,h⟩ else .inl false

private lemma raw_eq {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = (raw (n:=n) i).elim id x := by
  by_cases h : i<n
  · rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using h),List.getElem_ofFn]
    simp [raw,h]
  · rw [List.getD_eq_default (List.ofFn x) false (by simpa using Nat.le_of_not_lt h)]
    simp [raw,h]

private lemma classify_pair {n : ℕ} (a b : Bool ⊕ Fin n) (join : Bool) :
    HeadForm (fun x : Fin n → Bool => if join then (a.elim id x || b.elim id x) else
                                                   (a.elim id x && b.elim id x)) := by
  cases a with
  | inl u =>
    cases u <;> cases join
    · exact .flat (.inl false) (by simp)
    · exact .flat b (by simp)
    · exact .flat b (by simp)
    · exact .flat (.inl true) (by simp)
  | inr p =>
    cases b with
    | inl v =>
      cases v <;> cases join
      · exact .flat (.inl false) (by simp)
      · exact .flat (.inr p) (by simp)
      · exact .flat (.inr p) (by simp)
      · exact .flat (.inl true) (by simp)
    | inr q =>
      by_cases eq : p=q
      · subst q; exact .flat (.inr p) (by cases join <;> simp)
      · cases join
        · exact .conj p q eq (by simp)
        · exact .disj p q eq (by simp)

lemma classify {n : ℕ} (g : Gate)
    (allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2) :
    HeadForm (@firstVal n g) := by
  have fv : @firstVal n g = fun x => g.op.eval (g.inputs.map fun i => (raw (n:=n) i).elim id x) := by
    funext x
    unfold firstVal
    exact congrArg g.op.eval (List.map_congr_left (fun i _ => raw_eq x i))
  rw [fv]
  rcases allowed with hop|hop|hop
  · rcases ins : g.inputs with _ | ⟨i,_|⟨j,_|⟨k,ks⟩⟩⟩
    · exact .flat (.inl true) (by simp [firstVal,hop,ins,GateOp.eval])
    · exact .flat (raw i) (by simp [firstVal,hop,ins,GateOp.eval,raw_eq])
    · simpa [hop,ins,GateOp.eval] using classify_pair (raw (n:=n) i) (raw j) false
    · simp [ins] at arity
  · rcases ins : g.inputs with _ | ⟨i,_|⟨j,_|⟨k,ks⟩⟩⟩
    · exact .flat (.inl false) (by simp [firstVal,hop,ins,GateOp.eval])
    · exact .flat (raw i) (by simp [firstVal,hop,ins,GateOp.eval,raw_eq])
    · simpa [hop,ins,GateOp.eval] using classify_pair (raw (n:=n) i) (raw j) true
    · simp [ins] at arity
  · cases ins : g.inputs with
    | nil => exact .flat (.inl true) (by simp [firstVal,hop,ins,GateOp.eval])
    | cons i is =>
      cases eq : raw (n:=n) i with
      | inl b => exact .flat (.inl (!b)) (by simp [firstVal,hop,ins,GateOp.eval,raw_eq,eq])
      | inr p => exact .neg p (by simp [firstVal,hop,ins,GateOp.eval,raw_eq,eq])

private lemma sum_single {n : ℕ} (S : Finset (Fin n)) (q : Fin n) :
    sumRow S (fun p => decide (p=q)) = decide (q ∈ S) := by simp [sumRow]

private lemma distinguish {n r : ℕ} (S : Fin r → Finset (Fin n)) (j : Fin r) (p : Fin n)
    (mem : p ∈ S j) (d : Bool ⊕ Fin n) (g : Gate) (u : Fin n → Bool)
    (off : sumRow (S j) u = false)
    (persist : ∀ a, d = .inr a → firstVal g u = firstVal g (Function.update u p true)) :
    ∃ (j : Fin r) (u v : Fin n → Bool), (∀ i, i ≠ p → u i = v i) ∧
      (∀ a, d = .inr a → firstVal g u = firstVal g v) ∧ sumRow (S j) u ≠ sumRow (S j) v := by
  refine ⟨j,u,Function.update u p true,fun i hi => (Function.update_of_ne hi _ _).symm,persist,?_⟩
  have on' : sumRow (S j) (Function.update u p true) = true :=
    decide_eq_true ⟨p,mem,Function.update_self ..⟩
  simp [off,on']

def degree {n r : ℕ} (S : Fin r → Finset (Fin n)) (p : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => p ∈ S j)).card

lemma separated {n r : ℕ} (S : Fin r → Finset (Fin n))
    (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) {p q : Fin n} (diff : p ≠ q)
    (two : 2 ≤ degree S p) : ∃ i, p ∈ S i ∧ q ∉ S i := by
  obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp two
  have pi := (Finset.mem_filter.mp hi).2
  have pj := (Finset.mem_filter.mp hj).2
  by_cases qi : q ∈ S i
  · refine ⟨j,pj,fun qj => diff ?_⟩
    exact Finset.card_le_one.mp (linear i j ij) _ (Finset.mem_inter.mpr ⟨pi,pj⟩)
      _ (Finset.mem_inter.mpr ⟨qi,qj⟩)
  · exact ⟨i,pi,qi⟩

/-- In a linear set family with rows of size at least two, bypassing the first gate
either shortens the circuit outright or removes one input p. Removing p saves two
gates whenever p occurs in at least two rows. Negations are unrestricted. -/
theorem head_reduction {n r : ℕ} (S : Fin r → Finset (Fin n))
    (two : ∀ j, 2 ≤ (S j).card) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (g : Gate) (gs : List Gate) (out : Fin r → ℕ) (hf : FanInTwo ⟨g::gs,0⟩)
    (hc : ∀ j x, (Circuit.mk (g::gs) (out j)).eval (List.ofFn x) = sumRow (S j) x) :
    (∃ (hs : List Gate) (o : Fin r → ℕ), hs.length ≤ gs.length ∧ FanInTwo ⟨hs,0⟩ ∧
      ∀ j x, (Circuit.mk hs (o j)).eval (List.ofFn x) = sumRow (S j) x) ∨
    (∃ (p : Fin n) (hs : List Gate) (o : Fin r → ℕ), hs.length ≤ gs.length ∧
      (2 ≤ degree S p → hs.length+1 ≤ gs.length) ∧ FanInTwo ⟨hs,0⟩ ∧
      ∀ j x, (Circuit.mk hs (o j)).eval (List.ofFn x) = sumRow ((S j).erase p) x) := by
  classical
  have non (p : Fin n) (j : Fin r) : ((S j).erase p).Nonempty := by
    apply Finset.card_pos.mp
    have h := two j
    by_cases mem : p ∈ S j
    · rw [Finset.card_erase_of_mem mem]; omega
    · simpa [Finset.erase_eq_of_notMem mem] using Nat.zero_lt_of_lt h
  have cut (p : Fin n) (d : Bool ⊕ Fin n)
      (bypass : ∀ x : Fin n → Bool, firstVal g (eraseBit p x) = d.elim id x)
      (test : 2 ≤ degree S p → ∃ (j : Fin r) (u v : Fin n → Bool),
        (∀ i, i ≠ p → u i = v i) ∧ (∀ a, d = .inr a → firstVal g u = firstVal g v) ∧
        sumRow (S j) u ≠ sumRow (S j) v) :
      ∃ (hs : List Gate) (o : Fin r → ℕ), hs.length ≤ gs.length ∧
        (2 ≤ degree S p → hs.length+1 ≤ gs.length) ∧ FanInTwo ⟨hs,0⟩ ∧
        ∀ j x, (Circuit.mk hs (o j)).eval (List.ofFn x) = sumRow ((S j).erase p) x := by
    obtain ⟨hs,o,weak,ok,he,strong⟩ := erase_after_first S p d g gs out hf hc (non p) bypass
    exact ⟨hs,o,by simpa using weak,fun h => by simpa using strong (test h),ok,he⟩
  have positive (p : Fin n) (h : 2 ≤ degree S p) : ∃ j, p ∈ S j := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  have hg := hf g List.mem_cons_self
  cases classify (n:=n) g hg.1 hg.2 with
  | flat d h =>
    left
    let σ : Fin (n+1) → Bool ⊕ Fin n := Fin.snoc Sum.inr d
    have eq (x : Fin n → Bool) : assignInput σ x = Fin.snoc x (firstVal g x) := by
      funext i
      exact Fin.lastCases (by simp [assignInput,σ,h]) (fun j => by simp [assignInput,σ]) i
    have ev (j) (x) : (Circuit.mk gs (out j)).eval (List.ofFn (assignInput σ x)) = sumRow (S j) x := by
      rw [eq,tail_eq,hc]
    obtain ⟨hs,o,ok,le,eval,_⟩ := specialize_outputs σ gs out (fun a ha => hf a (List.mem_cons_of_mem _ ha))
      (fun j => ⟨fun _ => false,fun _ => true,by simp only [ev]; exact sum_vary (Finset.card_pos.mp (Nat.zero_lt_of_lt (two j)))⟩)
    exact ⟨hs,o,le,ok,fun j x => (eval j x).trans (ev j x)⟩
  | neg p h =>
    right; refine ⟨p,cut p (.inl true) (fun x => by simp [h,eraseBit]) ?_⟩
    intro hp
    obtain ⟨j,mem⟩ := positive p hp
    exact distinguish S j p mem _ g (fun _ => false) (by simp [sumRow]) (by simp)
  | conj p q diff h =>
    right; refine ⟨p,cut p (.inl false) (fun x => by simp [h,eraseBit]) ?_⟩
    intro hp
    obtain ⟨j,mem⟩ := positive p hp
    exact distinguish S j p mem _ g (fun _ => false) (by simp [sumRow]) (by simp)
  | disj p q diff h =>
    right; refine ⟨p,cut p (.inr q) (fun x => by simp [h,eraseBit,diff.symm]) ?_⟩
    intro hp
    obtain ⟨j,mem,missing⟩ := separated S linear diff hp
    apply distinguish S j p mem _ g (fun i => decide (i=q))
    · simp [sum_single,missing]
    · intro a _
      simp [h,Function.update_of_ne diff.symm]

theorem subdegree {n r s : ℕ} (S : Fin r → Finset (Fin n)) (T : Fin s → Finset (Fin n))
    (f : Fin s → Fin r) (inj : Function.Injective f) (sub : ∀ i, T i ⊆ S (f i)) (p : Fin n) :
    degree T p ≤ degree S p := by
  classical
  let A := Finset.univ.filter (fun i => p ∈ T i)
  let B := Finset.univ.filter (fun j => p ∈ S j)
  let lift (i : ↥A) : ↥B := ⟨f i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub _ (Finset.mem_filter.mp i.property).2⟩⟩
  have one : Function.Injective lift := fun i j h => Subtype.ext (inj (congrArg Subtype.val h))
  change A.card ≤ B.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift one

private lemma erased_count {n r : ℕ} (S : Fin r → Finset (Fin n)) (two : ∀ i, 2 ≤ (S i).card) (p : Fin n) :
    (∑ i, ((S i).card-1)) = (∑ i, (((S i).erase p).card-1)) + degree S p := by
  classical
  have step (i : Fin r) : (S i).card-1 = (((S i).erase p).card-1) + (if p ∈ S i then 1 else 0) := by
    have h := two i
    by_cases e : p ∈ S i
    · rw [Finset.card_erase_of_mem e,if_pos e]; omega
    · simp [e,Finset.erase_eq_of_notMem e]
  rw [Finset.sum_congr rfl (fun i _ => step i),Finset.sum_add_distrib]
  simp [degree]

/-- When every point belongs to at most two rows of a linear set family, no shared
AND/OR/NOT circuit improves on independent row OR trees, with arbitrary row size.
Singleton and empty rows cost zero in this lower bound. -/
theorem degree_two {n r : ℕ} (S : Fin r → Finset (Fin n))
    (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (bound : ∀ p, degree S p ≤ 2)
    (gs0 : List Gate) (out0 : Fin r → ℕ) (hf0 : FanInTwo ⟨gs0,0⟩)
    (hc0 : ∀ j x, (Circuit.mk gs0 (out0 j)).eval (List.ofFn x) = sumRow (S j) x) :
    (∑ i, ((S i).card-1)) ≤ gs0.length := by
  classical
  suffices main : ∀ k (n r : ℕ) (S : Fin r → Finset (Fin n))
      (_ : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (_ : ∀ p, degree S p ≤ 2)
      (gs : List Gate) (out : Fin r → ℕ) (_ : gs.length = k) (_ : FanInTwo ⟨gs,0⟩)
      (_ : ∀ j x, (Circuit.mk gs (out j)).eval (List.ofFn x) = sumRow (S j) x),
      (∑ i, ((S i).card-1)) ≤ gs.length from main _ n r S linear bound gs0 out0 rfl hf0 hc0
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro n r S lin deg gs out len ok ev
    let A := Finset.univ.filter (fun i => 2 ≤ (S i).card)
    let e : Fin A.card ≃ ↥A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
    let ix (i : Fin A.card) := (e i).val
    let F (i : Fin A.card) := S (ix i)
    let o (i : Fin A.card) := out (ix i)
    have ii : Function.Injective ix := Subtype.val_injective.comp e.injective
    have two (i : Fin A.card) : 2 ≤ (F i).card := (Finset.mem_filter.mp (e i).property).2
    have thin (i j : Fin A.card) (ne : i ≠ j) : (F i ∩ F j).card ≤ 1 := lin _ _ (fun eq => ne (ii eq))
    have lim (p : Fin n) : degree F p ≤ 2 := (subdegree S F ix ii (fun _ => Finset.Subset.rfl) p).trans (deg p)
    have cost : (∑ i, ((F i).card-1)) = ∑ j, ((S j).card-1) := calc
      _ = ∑ a : ↥A, ((S a.val).card-1) := e.sum_comp (fun a => (S a.val).card-1)
      _ = ∑ a ∈ A, ((S a).card-1) := Finset.sum_attach A (fun a => (S a).card-1)
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
        intro a _ ha
        have small : ¬ 2 ≤ (S a).card := fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
        omega)
    rw [←cost]
    cases gs with
    | nil =>
      have semantic (i : Fin A.card) (x : Fin n → Bool) :
          ((Circuit.mk [] 0).wires (List.ofFn x)).getD (o i) false = true ↔ ∃ p ∈ F i, x p = true := by
        change (Circuit.mk [] (out (ix i))).eval (List.ofFn x) = true ↔ _
        rw [ev]; simp [F,sumRow]
      have z := (PlaneResearch.TripleSystems.Unrestricted.unrestricted_rows n A.card F two thin
        ⟨[],0⟩ o ok semantic).1
      change A.card + _ ≤ 0 at z
      have empty (i : Fin A.card) : False := by have := i.isLt; omega
      exact le_of_eq (Finset.sum_eq_zero (fun i _ => (empty i).elim))
    | cons g gs =>
      rcases head_reduction F two thin g gs o ok (fun i => ev (ix i)) with
        ⟨hs,o',hshort,hf,he⟩ | ⟨p,hs,o',hshort,extra,hf,he⟩
      · have lt : hs.length < k := by simp only [List.length_cons] at len; omega
        have h := ih _ lt n _ F thin lim hs o' rfl hf he
        simp only [List.length_cons]; omega
      · let R i := (F i).erase p
        have sub (i) : R i ⊆ F i := Finset.erase_subset _ _
        have lineR (i j) (ij : i ≠ j) : (R i ∩ R j).card ≤ 1 :=
          (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ij)
        have limR (q : Fin n) : degree R q ≤ 2 := (subdegree F R id Function.injective_id sub q).trans (lim q)
        have lt : hs.length < k := by simp only [List.length_cons] at len; omega
        have res := ih _ lt n _ R lineR limR hs o' rfl hf he
        rw [erased_count F two p]
        change (∑ i, ((R i).card-1)) + degree F p ≤ gs.length+1
        have cap := lim p
        by_cases h : 2 ≤ degree F p
        · have second := extra h; omega
        · omega

end PlaneResearch.InputDegree
