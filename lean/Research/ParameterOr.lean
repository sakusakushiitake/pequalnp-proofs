import Research.DegreeTwoOr

namespace PlaneResearch.ParameterOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection PlaneResearch.InputDegree

abbrev Scalar (Z : Type) (n : ℕ) := Fin n ⊕ (Z → Bool)

def encode {Z : Type} {n k : ℕ} (names : Fin k → Scalar Z n)
    (x : Fin n → Bool) (z : Z) (i : Fin k) : Bool := (names i).elim x (fun f => f z)

def target {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool) (x : Fin n → Bool) (z : Z) : Bool :=
  sumRow S x || P z

noncomputable def weight {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool) : ℕ := by
  classical
  exact S.card + (if ∃ z, P z = true then 1 else 0) - 1

private abbrev eraseBit {n : ℕ} (p : Fin n) (x : Fin n → Bool) := Function.update x p false

private lemma erased {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool) (p : Fin n) (x : Fin n → Bool) (z : Z) :
    target S P (eraseBit p x) z = target (S.erase p) P x z := by
  unfold target
  congr 1
  simp only [sumRow,decide_eq_decide]
  constructor
  · rintro ⟨a,ha,on'⟩
    have ne : a ≠ p := by rintro rfl; simp [eraseBit] at on'
    exact ⟨a,Finset.mem_erase.mpr ⟨ne,ha⟩,by simpa [eraseBit,ne] using on'⟩
  · rintro ⟨a,ha,on'⟩
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
    exact ⟨a,mem,by simpa [eraseBit,ne] using on'⟩

private lemma vary {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool) (z0 : Z)
    (base : P z0 = false) (pos : 0 < weight S P) (p : Fin n) :
    ∃ x y z w, target (S.erase p) P x z ≠ target (S.erase p) P y w := by
  classical
  by_cases active : ∃ z, P z = true
  · obtain ⟨w,hw⟩ := active
    exact ⟨fun _ => false,fun _ => false,z0,w,by simp [target,sumRow,base,hw]⟩
  · have size : 2 ≤ S.card := by simp [weight,active] at pos; omega
    have rem : (S.erase p).Nonempty := by
      apply Finset.card_pos.mp
      by_cases mem : p ∈ S
      · rw [Finset.card_erase_of_mem mem]; omega
      · simpa [Finset.erase_eq_of_notMem mem] using Nat.zero_lt_of_lt size
    exact ⟨fun _ => false,fun _ => true,z0,z0,by simpa [target,sumRow,base,Finset.Nonempty] using rem⟩

private noncomputable def pins {Z : Type} {n k : ℕ} (names : Fin k → Scalar Z n)
    (p : Fin n) (d : Bool ⊕ Fin k) : Fin (k+1) → Bool ⊕ Fin k := by
  classical
  exact Fin.snoc (fun i => if names i = .inl p then .inl false else .inr i) d

private lemma pin_values {Z : Type} {n k : ℕ} (names : Fin k → Scalar Z n) (p : Fin n)
    (d : Bool ⊕ Fin k) (x : Fin n → Bool) (z : Z) :
    assignInput (pins names p d) (encode names x z) =
      Fin.snoc (encode names (eraseBit p x) z) (d.elim id (encode names x z)) := by
  classical
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [assignInput,pins]
  · cases eq : names j with
    | inl q => by_cases same : q=p <;> simp [assignInput,pins,encode,eq,same,eraseBit]
    | inr f => simp [assignInput,pins,encode,eq]

private abbrev Tests {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (names : Fin k → Scalar Z n) (p : Fin n) (d : Bool ⊕ Fin k) (g : Gate) :=
  ∃ (j : Fin r) (z : Z) (u v : Fin n → Bool), (∀ i, i ≠ p → u i = v i) ∧
    (∀ a, d = .inr a → firstVal g (encode names u z) = firstVal g (encode names v z)) ∧
    target (S j) (P j) u z ≠ target (S j) (P j) v z

private lemma vary_live {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool) (z0 : Z)
    (base : P z0 = false) (live : 0 < weight S P ∨ ∃ z, P z = true) (p : Fin n) :
    ∃ x y z w, target (S.erase p) P x z ≠ target (S.erase p) P y w := by
  rcases live with h|⟨w,hw⟩
  · exact vary S P z0 base h p
  · exact ⟨fun _ => false,fun _ => false,z0,w,by simp [target,sumRow,base,hw]⟩

private lemma erase_head {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (z0 : Z) (base : ∀ j, P j z0 = false) (pos : ∀ j, 0 < weight (S j) (P j) ∨ ∃ z, P j z = true)
    (names : Fin k → Scalar Z n) (g : Gate) (gs : List Gate) (out : Fin r → ℕ)
    (hf : FanInTwo ⟨g::gs,0⟩) (hc : ∀ j x z, (Circuit.mk (g::gs) (out j)).eval (List.ofFn (encode names x z)) =
      target (S j) (P j) x z) (p : Fin n) (d : Bool ⊕ Fin k)
    (bypass : ∀ x z, firstVal g (encode names (eraseBit p x) z) = d.elim id (encode names x z))
    (test : 2 ≤ degree S p → Tests S P names p d g) :
    ∃ (hs : List Gate) (o : Fin r → ℕ), hs.length ≤ gs.length ∧
      (2 ≤ degree S p → hs.length+1 ≤ gs.length) ∧ FanInTwo ⟨hs,0⟩ ∧
      ∀ j x z, (Circuit.mk hs (o j)).eval (List.ofFn (encode names x z)) = target ((S j).erase p) (P j) x z := by
  classical
  have ev (j : Fin r) (x : Fin n → Bool) (z : Z) : (Circuit.mk gs (out j)).eval
      (List.ofFn (assignInput (pins names p d) (encode names x z))) = target ((S j).erase p) (P j) x z := by
    rw [pin_values,← bypass,tail_eq,hc,erased]
  have non (j : Fin r) := vary_live (S j) (P j) z0 (base j) (pos j) p
  obtain ⟨hs,o,ok,weak,hev,less⟩ := specialize_outputs (pins names p d) gs out
    (fun a ha => hf a (List.mem_cons_of_mem _ ha)) (fun j => by
      obtain ⟨x,y,z,w,h⟩ := non j
      exact ⟨encode names x z,encode names y w,by simpa only [ev] using h⟩)
  refine ⟨hs,o,weak,?_,ok,fun j x z => (hev j _).trans (ev j x z)⟩
  intro hp
  apply less
  obtain ⟨j,z,u,v,away,last,diff⟩ := test hp
  let U := encode names u z
  let V := encode names v z
  refine ⟨j,Fin.snoc U (firstVal g U),Fin.snoc V (firstVal g V),?_,?_⟩
  · intro i a
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa [pins,U,V] using last a
    · cases eq : names k with
      | inl t => by_cases same : t=p <;> simp [pins,U,V,encode,eq,same,away]
      | inr f => simp [pins,U,V,encode,eq]
  · simpa only [U,V,tail_eq,hc] using diff

private inductive Move {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (names : Fin k → Scalar Z n) (g : Gate) : Prop where
  | free (v : Scalar Z n) (h : ∀ x z, firstVal g (encode names x z) = v.elim x (fun f => f z))
  | zero (p : Fin n) (d : Bool ⊕ Fin k)
      (h : ∀ x z, firstVal g (encode names (eraseBit p x) z) = d.elim id (encode names x z))
      (test : 2 ≤ degree S p → Tests S P names p d g)

private lemma tests_of {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (names : Fin k → Scalar Z n) (p : Fin n) (d : Bool ⊕ Fin k) (g : Gate) (j : Fin r)
    (mem : p ∈ S j) (z : Z) (u : Fin n → Bool) (off : target (S j) (P j) u z = false)
    (sat : ∀ a, d = .inr a → firstVal g (encode names u z) =
      firstVal g (encode names (Function.update u p true) z)) : Tests S P names p d g := by
  refine ⟨j,z,u,Function.update u p true,fun i hi => (Function.update_of_ne hi _ _).symm,sat,?_⟩
  have one : sumRow (S j) (Function.update u p true) = true := decide_eq_true ⟨p,mem,Function.update_self ..⟩
  rw [off]
  simp [target,one]

private theorem choose_move {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (z0 : Z) (base : ∀ j, P j z0 = false)
    (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (apart : ∀ i j, i ≠ j → ∀ p ∈ S i, p ∈ S j → ∀ z, P i z = false ∨ P j z = false)
    (names : Fin k → Scalar Z n) (g : Gate)
    (allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2) :
    Move S P names g := by
  classical
  have constant (p : Fin n) (b : Bool)
      (fix : ∀ x z, firstVal g (encode names (eraseBit p x) z) = b) : Move S P names g := by
    apply Move.zero p (.inl b) fix
    intro hp
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hp)
    exact tests_of S P names p (.inl b) g j (Finset.mem_filter.mp hj).2 z0 (fun _ => false)
      (by simp [target,sumRow,base]) (by simp)
  have either (p : Fin n) (a : Fin k)
      (op : ∀ x z, firstVal g (encode names x z) = (x p || encode names x z a)) : Move S P names g := by
    cases eq : names a with
    | inl q =>
      by_cases same : p=q
      · exact .free (.inl p) (by intro x z; simp [op,encode,eq,←same])
      apply Move.zero p (.inr a) (by intro x z; simp [op,encode,eq,eraseBit,Ne.symm same])
      intro hp
      obtain ⟨j,mem,miss⟩ := separated S linear same hp
      apply tests_of S P names p _ g j mem z0 (fun i => decide (i=q))
      · simp [target,sumRow,miss,base]
      · intro i _; simp [op,encode,eq,Function.update_of_ne (Ne.symm same)]
    | inr f =>
      by_cases active : ∃ z, f z = true
      · obtain ⟨z,on'⟩ := active
        apply Move.zero p (.inr a) (by intro x w; simp [op,encode,eq,eraseBit])
        intro hp
        obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp hp
        have pi := (Finset.mem_filter.mp hi).2
        have pj := (Finset.mem_filter.mp hj).2
        obtain ⟨o,mem,off⟩ : ∃ o, p ∈ S o ∧ P o z = false := by
          rcases apart i j ij p pi pj z with h|h
          · exact ⟨i,pi,h⟩
          · exact ⟨j,pj,h⟩
        apply tests_of S P names p _ g o mem z (fun _ => false)
        · simp [target,sumRow,off]
        · intro i _; simp [op,encode,eq,on']
      · have falseAll (z : Z) : f z = false := Bool.eq_false_iff.mpr (fun h => active ⟨z,h⟩)
        exact .free (.inl p) (by intro x z; simp [op,encode,eq,falseAll])
  cases classify (n:=k) g allowed arity with
  | flat d h =>
    cases d with
    | inl b => exact .free (.inr (fun _ => b)) (by simp [h])
    | inr i => exact .free (names i) (by simp [h,encode])
  | neg a h =>
    cases eq : names a with
    | inl p => exact constant p true (by simp [h,encode,eq,eraseBit])
    | inr f => exact .free (.inr (fun z => !(f z))) (by simp [h,encode,eq])
  | conj a b _ h =>
    cases ea : names a with
    | inl p =>
      apply constant p false
      intro x z
      rw [h]
      have off : encode names (eraseBit p x) z a = false := by simp [encode,ea,eraseBit]
      simp only [off,Bool.false_and]
    | inr f =>
      cases eb : names b with
      | inl q =>
        apply constant q false
        intro x z
        rw [h]
        have off : encode names (eraseBit q x) z b = false := by simp [encode,eb,eraseBit]
        simp only [off,Bool.and_false]
      | inr f' => exact .free (.inr (fun z => f z && f' z)) (by simp [h,encode,ea,eb])
  | disj a b _ h =>
    cases ea : names a with
    | inl p => exact either p b (by simp [h,encode,ea])
    | inr f =>
      cases eb : names b with
      | inl q => exact either q a (by simp [h,encode,ea,eb,Bool.or_comm])
      | inr f' => exact .free (.inr (fun z => f z || f' z)) (by simp [h,encode,ea,eb])

private lemma no_scalar {Z : Type} {n : ℕ} (S : Finset (Fin n)) (P : Z → Bool)
    (z0 : Z) (base : P z0 = false) (pos : 0 < weight S P) (v : Scalar Z n)
    (same : ∀ x z, v.elim x (fun f => f z) = target S P x z) : False := by
  classical
  cases v with
  | inr f =>
    have live : S.Nonempty := by
      by_contra h
      have empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      by_cases e : ∃ z, P z = true <;> simp [weight,empty,e] at pos
    obtain ⟨p,hp⟩ := live
    have a := same (fun _ => false) z0
    have b := same (fun i => decide (i=p)) z0
    simp [target,sumRow,base,hp] at a b
    simp [a] at b
  | inl p =>
    have off (x : Fin n → Bool) (z : Z) : target (S.erase p) P x z = false := by
      simpa [erased,eraseBit,Function.update_self] using (same (eraseBit p x) z).symm
    obtain ⟨x,y,z,w,ne⟩ := vary S P z0 base pos p
    exact ne ((off x z).trans (off y w).symm)

private lemma cost_drop {Z : Type} {n r : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (pos : ∀ j, 0 < weight (S j) (P j) ∨ ∃ z, P j z = true) (p : Fin n) :
    (∑ i, weight (S i) (P i)) = (∑ i, weight ((S i).erase p) (P i)) + degree S p := by
  classical
  have each (i : Fin r) : weight (S i) (P i) = weight ((S i).erase p) (P i) + (if p ∈ S i then 1 else 0) := by
    by_cases mem : p ∈ S i
    · have card := Finset.card_pos.mpr (show (S i).Nonempty from ⟨p,mem⟩)
      have h : 0 < weight (S i) (P i) := (pos i).elim id (fun e => by simpa [weight,e] using card)
      by_cases e : ∃ z, P i z = true <;> simp [weight,e,mem,Finset.card_erase_of_mem mem] at h ⊢ <;> omega
    · simp [Finset.erase_eq_of_notMem mem,mem]
  rw [Finset.sum_congr rfl (fun i _ => each i),Finset.sum_add_distrib]
  simp [degree]

/-- Boolean side information depending on a common parameter may be supplied for free.
Any two rows sharing a counted input must have disjoint true parameter states.
The cardinality lower bound counts each active row as if it had one extra point. -/
theorem parameter_lower {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (z0 : Z) (base : ∀ j, P j z0 = false) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (apart : ∀ i j, i ≠ j → ∀ p ∈ S i, p ∈ S j → ∀ z, P i z = false ∨ P j z = false)
    (bound : ∀ p, degree S p ≤ 2) (names : Fin k → Scalar Z n) (gs0 : List Gate) (out0 : Fin r → ℕ)
    (hf0 : FanInTwo ⟨gs0,0⟩) (hc0 : ∀ j x z, (Circuit.mk gs0 (out0 j)).eval (List.ofFn (encode names x z)) =
      target (S j) (P j) x z) : (∑ i, weight (S i) (P i)) ≤ gs0.length := by
  classical
  suffices main : ∀ t (r k : ℕ) (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
      (_ : ∀ j, P j z0 = false) (_ : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
      (_ : ∀ i j, i ≠ j → ∀ p ∈ S i, p ∈ S j → ∀ z, P i z = false ∨ P j z = false)
      (_ : ∀ p, degree S p ≤ 2) (names : Fin k → Scalar Z n) (gs : List Gate) (out : Fin r → ℕ)
      (_ : gs.length=t) (_ : FanInTwo ⟨gs,0⟩) (_ : ∀ j x z, (Circuit.mk gs (out j)).eval
        (List.ofFn (encode names x z)) = target (S j) (P j) x z), (∑ i, weight (S i) (P i)) ≤ gs.length from
    main _ r k S P base linear apart bound names gs0 out0 rfl hf0 hc0
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro r k S P base lin apart deg names gs out len ok hc
    let A := Finset.univ.filter (fun i => 0 < weight (S i) (P i))
    let e : Fin A.card ≃ ↥A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
    let ix (i : Fin A.card) := (e i).val
    let F (i : Fin A.card) := S (ix i)
    let Q (i : Fin A.card) := P (ix i)
    let o (i : Fin A.card) := out (ix i)
    have ii : Function.Injective ix := Subtype.val_injective.comp e.injective
    have good (i : Fin A.card) : 0 < weight (F i) (Q i) := (Finset.mem_filter.mp (e i).property).2
    have thin (i j : Fin A.card) (ne : i ≠ j) : (F i ∩ F j).card ≤ 1 := lin _ _ (fun eq => ne (ii eq))
    have ap (i j : Fin A.card) (ne : i ≠ j) := apart (ix i) (ix j) (fun eq => ne (ii eq))
    have lim (p : Fin n) : degree F p ≤ 2 := (subdegree S F ix ii (fun _ => Finset.Subset.rfl) p).trans (deg p)
    have cost : (∑ i, weight (F i) (Q i)) = ∑ i, weight (S i) (P i) := calc
      _ = ∑ a : ↥A, weight (S a.val) (P a.val) := e.sum_comp (fun a => weight (S a.val) (P a.val))
      _ = ∑ a ∈ A, weight (S a) (P a) := Finset.sum_attach A (fun a => weight (S a) (P a))
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
        intro a _ ha
        exact Nat.eq_zero_of_not_pos (fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)))
    rw [←cost]
    cases gs with
    | nil =>
      have empty (i : Fin A.card) : False := by
        by_cases hi : o i < k
        · apply no_scalar (F i) (Q i) z0 (base _) (good i) (names ⟨o i,hi⟩)
          intro x z
          have h := hc (ix i) x z
          change (List.ofFn (encode names x z)).getD (o i) false = _ at h
          rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn] at h
          exact h
        · apply no_scalar (F i) (Q i) z0 (base _) (good i) (.inr (fun _ => false))
          intro x z
          have h := hc (ix i) x z
          change (List.ofFn (encode names x z)).getD (o i) false = _ at h
          rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)] at h
          exact h
      exact le_of_eq (Finset.sum_eq_zero (fun i _ => (empty i).elim))
    | cons g gs =>
      have hg := ok g List.mem_cons_self
      cases choose_move F Q z0 (fun i => base (ix i)) thin ap names g hg.1 hg.2 with
      | free v hv =>
        let nm : Fin (k+1) → Scalar Z n := Fin.snoc names v
        have eq (x : Fin n → Bool) (z : Z) : encode nm x z = Fin.snoc (encode names x z) (firstVal g (encode names x z)) := by
          funext i
          exact Fin.lastCases (by simp [nm,encode,hv]) (fun j => by simp [nm,encode]) i
        have lt : gs.length < t := by simp only [List.length_cons] at len; omega
        have h := ih _ lt _ _ F Q (fun i => base (ix i)) thin ap lim nm gs o rfl
          (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg')) (fun i x z => by rw [eq,tail_eq]; exact hc (ix i) x z)
        simp only [List.length_cons]; omega
      | zero p d bypass test =>
        obtain ⟨hs,o',weak,extra,hf,he⟩ := erase_head F Q z0 (fun i => base (ix i)) (fun i => Or.inl (good i)) names g gs o ok
          (fun i => hc (ix i)) p d bypass test
        let R i := (F i).erase p
        have sub (i) : R i ⊆ F i := Finset.erase_subset _ _
        have lr (i j) (ne : i ≠ j) : (R i ∩ R j).card ≤ 1 :=
          (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ne)
        have lt : hs.length < t := by simp only [List.length_cons] at len; omega
        have h := ih _ lt _ _ R Q (fun i => base (ix i)) lr
          (fun i j ne a ai aj => ap i j ne a (sub i ai) (sub j aj))
          (fun q => (subdegree F R id Function.injective_id sub q).trans (lim q)) names hs o' rfl hf he
        rw [cost_drop F Q (fun i => Or.inl (good i)) p]
        change (∑ i, weight (R i) (Q i)) + degree F p ≤ gs.length+1
        have cap := lim p
        by_cases hp : 2 ≤ degree F p
        · have save := extra hp; omega
        · omega

/-- The gates left over after paying for the low-degree input variables still compute
all parameter-only outputs on their original encoded inputs. -/
theorem compress_parameters {Z : Type} {n r k : ℕ} (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
    (z0 : Z) (base : ∀ j, P j z0 = false) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (apart : ∀ i j, i ≠ j → ∀ p ∈ S i, p ∈ S j → ∀ z, P i z = false ∨ P j z = false)
    (bound : ∀ p, degree S p ≤ 2) (names : Fin k → Scalar Z n) (gs0 : List Gate) (out0 : Fin r → ℕ)
    (hf0 : FanInTwo ⟨gs0,0⟩) (hc0 : ∀ j x z, (Circuit.mk gs0 (out0 j)).eval (List.ofFn (encode names x z)) =
      target (S j) (P j) x z) :
    ∃ (hs : List Gate) (o : Fin r → ℕ), FanInTwo ⟨hs,0⟩ ∧ hs.length + (∑ i, weight (S i) (P i)) ≤ gs0.length ∧
      ∀ i z, (Circuit.mk hs (o i)).eval (List.ofFn (encode names (fun _ => false) z)) = P i z := by
  classical
  suffices main : ∀ t (r k : ℕ) (S : Fin r → Finset (Fin n)) (P : Fin r → Z → Bool)
      (_ : ∀ j, P j z0 = false) (_ : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
      (_ : ∀ i j, i ≠ j → ∀ p ∈ S i, p ∈ S j → ∀ z, P i z = false ∨ P j z = false)
      (_ : ∀ p, degree S p ≤ 2) (names : Fin k → Scalar Z n) (gs : List Gate) (out : Fin r → ℕ)
      (_ : gs.length=t) (_ : FanInTwo ⟨gs,0⟩) (_ : ∀ j x z, (Circuit.mk gs (out j)).eval
        (List.ofFn (encode names x z)) = target (S j) (P j) x z), ∃ (hs : List Gate) (o : Fin r → ℕ), FanInTwo ⟨hs,0⟩ ∧
      hs.length + (∑ i, weight (S i) (P i)) ≤ gs.length ∧
      ∀ i z, (Circuit.mk hs (o i)).eval (List.ofFn (encode names (fun _ => false) z)) = P i z from
    main _ r k S P base linear apart bound names gs0 out0 rfl hf0 hc0
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro r k S P base lin apart deg names gs out len ok hc
    let A := Finset.univ.filter (fun i => 0 < weight (S i) (P i) ∨ ∃ z, P i z = true)
    let e : Fin A.card ≃ ↥A := (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm
    let ix (i : Fin A.card) := (e i).val
    let F (i : Fin A.card) := S (ix i)
    let Q (i : Fin A.card) := P (ix i)
    let o (i : Fin A.card) := out (ix i)
    have ii : Function.Injective ix := Subtype.val_injective.comp e.injective
    have good (i : Fin A.card) : 0 < weight (F i) (Q i) ∨ ∃ z, Q i z = true := (Finset.mem_filter.mp (e i).property).2
    have thin (i j : Fin A.card) (ne : i ≠ j) : (F i ∩ F j).card ≤ 1 := lin _ _ (fun eq => ne (ii eq))
    have ap (i j : Fin A.card) (ne : i ≠ j) := apart (ix i) (ix j) (fun eq => ne (ii eq))
    have lim (p : Fin n) : degree F p ≤ 2 := (subdegree S F ix ii (fun _ => Finset.Subset.rfl) p).trans (deg p)
    have cost : (∑ i, weight (F i) (Q i)) = ∑ i, weight (S i) (P i) := calc
      _ = ∑ a : ↥A, weight (S a.val) (P a.val) := e.sum_comp (fun a => weight (S a.val) (P a.val))
      _ = ∑ a ∈ A, weight (S a) (P a) := Finset.sum_attach A (fun a => weight (S a) (P a))
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
        intro a _ ha
        exact Nat.eq_zero_of_not_pos (fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl h⟩)))
    have extend (hs : List Gate) (sel : Fin A.card → ℕ)
        (he : ∀ i z, (Circuit.mk hs (sel i)).eval (List.ofFn (encode names (fun _ => false) z)) = Q i z) :
        ∃ os : Fin r → ℕ, ∀ i z, (Circuit.mk hs (os i)).eval (List.ofFn (encode names (fun _ => false) z)) = P i z := by
      let os (i : Fin r) := if h : i ∈ A then sel (e.symm ⟨i,h⟩) else k+hs.length
      refine ⟨os,fun i z => ?_⟩
      by_cases hi : i ∈ A
      · simpa [os,hi,Q,ix] using he (e.symm ⟨i,hi⟩) z
      · have off : P i z = false := Bool.eq_false_iff.mpr (fun h =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ⟨z,h⟩⟩))
        rw [off]
        change (PlaneResearch.TripleSystems.wiresFrom hs _).getD (os i) false = false
        apply List.getD_eq_default
        simp [os,hi,PlaneResearch.TripleSystems.length_wiresFrom]
    cases gs with
    | nil =>
      have zero (i : Fin A.card) : weight (F i) (Q i) = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro positive
        by_cases hi : o i < k
        · apply no_scalar (F i) (Q i) z0 (base _) positive (names ⟨o i,hi⟩)
          intro x z
          have h := hc (ix i) x z
          change (List.ofFn (encode names x z)).getD (o i) false = _ at h
          rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn] at h
          exact h
        · apply no_scalar (F i) (Q i) z0 (base _) positive (.inr (fun _ => false))
          intro x z
          have h := hc (ix i) x z
          change (List.ofFn (encode names x z)).getD (o i) false = _ at h
          rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)] at h
          exact h
      refine ⟨[],out,ok,?_,fun i z => ?_⟩
      · rw [←cost,Finset.sum_eq_zero (fun i _ => zero i)]; decide
      · simpa [target,sumRow] using hc i (fun _ => false) z
    | cons g gs =>
      have hg := ok g List.mem_cons_self
      cases choose_move F Q z0 (fun i => base (ix i)) thin ap names g hg.1 hg.2 with
      | free v hv =>
        let nm : Fin (k+1) → Scalar Z n := Fin.snoc names v
        have eq (x : Fin n → Bool) (z : Z) : encode nm x z = Fin.snoc (encode names x z) (firstVal g (encode names x z)) := by
          funext i
          exact Fin.lastCases (by simp [nm,encode,hv]) (fun j => by simp [nm,encode]) i
        have lt : gs.length < t := by simp only [List.length_cons] at len; omega
        obtain ⟨hs,sel,hf,le,eval⟩ := ih _ lt _ _ F Q (fun i => base (ix i)) thin ap lim nm gs o rfl
          (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg')) (fun i x z => by rw [eq,tail_eq]; exact hc (ix i) x z)
        have side (i : Fin A.card) (z : Z) : (Circuit.mk (g::hs) (sel i)).eval
            (List.ofFn (encode names (fun _ => false) z)) = Q i z := by
          rw [←tail_eq,←eq]
          exact eval i z
        obtain ⟨os,allok⟩ := extend (g::hs) sel side
        refine ⟨g::hs,os,?_,?_,allok⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl|h
          · exact hg
          · exact hf _ h
        · rw [←cost]; simp only [List.length_cons]; omega
      | zero p d bypass test =>
        obtain ⟨hs,o',weak,extra,hf,he⟩ := erase_head F Q z0 (fun i => base (ix i)) good names g gs o ok
          (fun i => hc (ix i)) p d bypass test
        let R i := (F i).erase p
        have sub (i) : R i ⊆ F i := Finset.erase_subset _ _
        have lr (i j) (ne : i ≠ j) : (R i ∩ R j).card ≤ 1 :=
          (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ne)
        have lt : hs.length < t := by simp only [List.length_cons] at len; omega
        obtain ⟨last,sel,okLast,lc,eval⟩ := ih _ lt _ _ R Q (fun i => base (ix i)) lr
          (fun i j ne a ai aj => ap i j ne a (sub i ai) (sub j aj))
          (fun q => (subdegree F R id Function.injective_id sub q).trans (lim q)) names hs o' rfl hf he
        obtain ⟨os,allok⟩ := extend last sel eval
        refine ⟨last,os,okLast,?_,allok⟩
        rw [←cost,cost_drop F Q good p]
        change last.length + ((∑ i, weight (R i) (Q i)) + degree F p) ≤ gs.length+1
        have cap := lim p
        by_cases hp : 2 ≤ degree F p
        · have save := extra hp; omega
        · omega

private noncomputable def sources {n : ℕ} (H : Finset (Fin n)) (p : Fin n) : Scalar (Option (Fin n)) n := by
  classical
  exact if p ∈ H then .inr (fun z => decide (z = some p)) else .inl p

private def onPart {n : ℕ} (T H : Finset (Fin n)) (z : Option (Fin n)) : Bool :=
  decide (∃ a ∈ T ∩ H, z = some a)

private lemma split_eval {n : ℕ} (T H : Finset (Fin n)) (x : Fin n → Bool) (z : Option (Fin n)) :
    sumRow T (encode (sources H) x z) = target (T \ H) (onPart T H) x z := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [sumRow,target,onPart,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,on'⟩
    by_cases high : p ∈ H
    · exact Or.inr ⟨p,Finset.mem_inter.mpr ⟨hp,high⟩,by simpa [encode,sources,high] using on'⟩
    · exact Or.inl ⟨p,Finset.mem_sdiff.mpr ⟨hp,high⟩,by simpa [encode,sources,high] using on'⟩
  · rintro (⟨p,mem,hp⟩ | ⟨p,mem,rfl⟩)
    · obtain ⟨row,low⟩ := Finset.mem_sdiff.mp mem
      exact ⟨p,row,by simpa [encode,sources,low] using hp⟩
    · obtain ⟨row,high⟩ := Finset.mem_inter.mp mem
      exact ⟨p,row,by simp [encode,sources,high]⟩

/-- Points of H may occur in arbitrarily many rows. In each row their possible
contribution to this lower bound is one point, even with arbitrarily many NOTs. -/
theorem high_points {n r : ℕ} (T : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (low : ∀ p ∉ H, degree T p ≤ 2)
    (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (T i) x) :
    (∑ i, (((T i \ H).card + min 1 (T i ∩ H).card)-1)) ≤ C.size := by
  classical
  let S (i : Fin r) := T i \ H
  let P (i : Fin r) := onPart (T i) H
  have sub (i) : S i ⊆ T i := Finset.sdiff_subset
  have l (i j) (ne : i ≠ j) : (S i ∩ S j).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ne)
  have degreeLow (p) : degree S p ≤ 2 := by
    by_cases high : p ∈ H
    · simp [degree,S,high]
    · exact (subdegree T S id Function.injective_id sub p).trans (low p high)
  have apart (i j) (ne : i ≠ j) (p) (pi : p ∈ S i) (pj : p ∈ S j) (z) : P i z = false ∨ P j z = false := by
    by_contra! bad
    obtain ⟨a,ai,za⟩ := of_decide_eq_true (show onPart (T i) H z = true from by simpa using bad.1)
    obtain ⟨b,bj,zb⟩ := of_decide_eq_true (show onPart (T j) H z = true from by simpa using bad.2)
    have ab : a=b := Option.some.inj (za.symm.trans zb)
    subst b
    have pa := Finset.card_le_one.mp (thin i j ne) _ (Finset.mem_inter.mpr ⟨sub i pi,sub j pj⟩)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ai).1,(Finset.mem_inter.mp bj).1⟩)
    exact (Finset.mem_sdiff.mp pi).2 (pa ▸ (Finset.mem_inter.mp ai).2)
  have w (i) : weight (S i) (P i) = ((T i \ H).card + min 1 (T i ∩ H).card)-1 := by
    by_cases h : (T i ∩ H).Nonempty
    · obtain ⟨a,ha⟩ := h
      have on' : ∃ z, P i z = true := ⟨some a,decide_eq_true ⟨a,ha,rfl⟩⟩
      simp [weight,on',S,Nat.min_eq_left (Finset.card_pos.mpr ⟨a,ha⟩)]
    · have empty := Finset.not_nonempty_iff_eq_empty.mp h
      have off : ¬ ∃ z, P i z = true := by simp [P,onPart,empty]
      simp [weight,off,empty,S]
  simp_rw [←w]
  exact parameter_lower S P none (fun i => by simp [P,onPart]) l apart degreeLow (sources H) C.gates out hf
    (fun i x z => (hc i _).trans (split_eval (T i) H x z))

/-- The separate-tree cost is exact when each row contains at most one high-degree point. -/
theorem one_high_per_row {n r : ℕ} (T : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (low : ∀ p ∉ H, degree T p ≤ 2)
    (one : ∀ i, (T i ∩ H).card ≤ 1) (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (T i) x) :
    (∑ i, ((T i).card-1)) ≤ C.size := by
  have cost (i) : ((T i \ H).card + min 1 (T i ∩ H).card) = (T i).card := by
    rw [Nat.min_eq_right (one i),Finset.card_sdiff_add_card_inter]
  simpa only [cost] using high_points T H thin low C out hf hc

private theorem high_residue {n r : ℕ} (T : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (low : ∀ p ∉ H, degree T p ≤ 2)
    (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (T i) x) :
    ∃ (gs : List Gate) (o : Fin r → ℕ), FanInTwo ⟨gs,0⟩ ∧
      gs.length + (∑ i, (((T i \ H).card + min 1 (T i ∩ H).card)-1)) ≤ C.size ∧
      ∀ i (z : Option (Fin n)), (Circuit.mk gs (o i)).eval (List.ofFn (encode (sources H) (fun _ => false) z)) =
        onPart (T i) H z := by
  classical
  let S (i : Fin r) := T i \ H
  let P (i : Fin r) := onPart (T i) H
  have sub (i) : S i ⊆ T i := Finset.sdiff_subset
  have l (i j) (ne : i ≠ j) : (S i ∩ S j).card ≤ 1 :=
    (Finset.card_le_card (Finset.inter_subset_inter (sub i) (sub j))).trans (thin i j ne)
  have degreeLow (p) : degree S p ≤ 2 := by
    by_cases high : p ∈ H
    · simp [degree,S,high]
    · exact (subdegree T S id Function.injective_id sub p).trans (low p high)
  have apart (i j) (ne : i ≠ j) (p) (pi : p ∈ S i) (pj : p ∈ S j) (z) : P i z = false ∨ P j z = false := by
    by_contra! bad
    obtain ⟨a,ai,za⟩ := of_decide_eq_true (show onPart (T i) H z = true from by simpa using bad.1)
    obtain ⟨b,bj,zb⟩ := of_decide_eq_true (show onPart (T j) H z = true from by simpa using bad.2)
    have ab : a=b := Option.some.inj (za.symm.trans zb)
    subst b
    have pa := Finset.card_le_one.mp (thin i j ne) _ (Finset.mem_inter.mpr ⟨sub i pi,sub j pj⟩)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ai).1,(Finset.mem_inter.mp bj).1⟩)
    exact (Finset.mem_sdiff.mp pi).2 (pa ▸ (Finset.mem_inter.mp ai).2)
  have w (i) : weight (S i) (P i) = ((T i \ H).card + min 1 (T i ∩ H).card)-1 := by
    by_cases h : (T i ∩ H).Nonempty
    · obtain ⟨a,ha⟩ := h
      have on' : ∃ z, P i z = true := ⟨some a,decide_eq_true ⟨a,ha,rfl⟩⟩
      simp [weight,on',S,Nat.min_eq_left (Finset.card_pos.mpr ⟨a,ha⟩)]
    · have empty := Finset.not_nonempty_iff_eq_empty.mp h
      have off : ¬ ∃ z, P i z = true := by simp [P,onPart,empty]
      simp [weight,off,empty,S]
  simp_rw [←w]
  exact compress_parameters S P none (fun i => by simp [P,onPart]) l apart degreeLow (sources H) C.gates out hf
    (fun i x z => (hc i _).trans (split_eval (T i) H x z))


private lemma bit_on {n : ℕ} (S H : Finset (Fin n)) (a : Fin n) :
    onPart S H (some a) = decide (a ∈ S ∩ H) := by simp [onPart]

private lemma marked_outputs {n r : ℕ} (S : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (gs : List Gate) (o : Fin r → ℕ)
    (he : ∀ i (z : Option (Fin n)), (Circuit.mk gs (o i)).eval (List.ofFn (encode (sources H) (fun _ => false) z)) =
      onPart (S i) H z) : (Finset.univ.filter (fun i => 2 ≤ (S i ∩ H).card)).card ≤ gs.length := by
  classical
  let A := Finset.univ.filter (fun i => 2 ≤ (S i ∩ H).card)
  let X (a : Fin n) := List.ofFn (encode (sources H) (fun _ => false) (some a))
  have high (i : ↥A) : 2 ≤ (S i.val ∩ H).card := (Finset.mem_filter.mp i.property).2
  have accepts (i : Fin r) (a : Fin n) : (Circuit.mk gs (o i)).eval (X a) = decide (a ∈ S i ∩ H) :=
    (he i (some a)).trans (bit_on _ _ _)
  have bounds (i : ↥A) : n ≤ o i.val ∧ o i.val < n+gs.length := by
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (high i)
    have on' (p : Fin n) (hp : p ∈ S i.val ∩ H) : (Circuit.mk gs (o i.val)).eval (X p) = true :=
      (accepts i.val p).trans (decide_eq_true hp)
    constructor
    · by_contra! small
      let w : Fin n := ⟨o i.val,small⟩
      have raw (p : Fin n) (hp : p ∈ S i.val ∩ H) : p=w := by
        have op := on' p hp
        change (PlaneResearch.TripleSystems.wiresFrom gs (X p)).getD (o i.val) false = true at op
        rw [PlaneResearch.TripleSystems.getD_wiresFrom_lt _ _ _ (by simpa [X] using small)] at op
        dsimp only [X] at op
        rw [List.getD_eq_getElem _ _ (by simpa using small),List.getElem_ofFn] at op
        by_cases wh : w ∈ H
        · simpa [encode,sources,w,show (⟨o i.val,small⟩ : Fin n) ∈ H from wh] using op
        · simp [encode,sources,w,show (⟨o i.val,small⟩ : Fin n) ∉ H from wh] at op
      exact ab ((raw a ha).trans (raw b hb).symm)
    · by_contra! large
      have op := on' a ha
      change (PlaneResearch.TripleSystems.wiresFrom gs (X a)).getD (o i.val) false = true at op
      rw [List.getD_eq_default _ _ (by simpa [PlaneResearch.TripleSystems.length_wiresFrom,X] using large)] at op
      contradiction
  let idx (i : ↥A) : Fin gs.length := ⟨o i.val-n,by obtain ⟨lo,hi⟩ := bounds i; omega⟩
  have inj : Function.Injective idx := by
    intro i j eq
    have h := congrArg Fin.val eq
    change o i.val-n = o j.val-n at h
    have same : o i.val = o j.val := by have := (bounds i).1; have := (bounds j).1; omega
    apply Subtype.ext
    by_contra ne
    have incl (a : Fin n) (ha : a ∈ S i.val ∩ H) : a ∈ S j.val := by
      have good := accepts i.val a
      rw [same,accepts,decide_eq_true ha] at good
      exact (Finset.mem_inter.mp (of_decide_eq_true good)).1
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (high i)
    exact ab (Finset.card_le_one.mp (thin i.val j.val ne)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1,incl a ha⟩)
      _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1,incl b hb⟩))
  change A.card ≤ gs.length
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective idx inj

/-- Rows get credit for up to two high-degree points in addition to all low-degree points.
Each row containing two high points needs its own non-input wire in the residual circuit. -/
theorem two_high_points {n r : ℕ} (S : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (low : ∀ p ∉ H, degree S p ≤ 2)
    (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, (((S i \ H).card + min 2 (S i ∩ H).card)-1)) ≤ C.size := by
  classical
  obtain ⟨gs,o,_,le,he⟩ := high_residue S H thin low C out hf hc
  have num := marked_outputs S H thin gs o he
  have each (i : Fin r) : ((S i \ H).card + min 2 (S i ∩ H).card)-1 =
      (((S i \ H).card + min 1 (S i ∩ H).card)-1) + (if 2 ≤ (S i ∩ H).card then 1 else 0) := by
    split <;> omega
  rw [Finset.sum_congr rfl (fun i _ => each i),Finset.sum_add_distrib]
  have hits : (∑ i : Fin r, if 2 ≤ (S i ∩ H).card then (1 : ℕ) else 0) =
      (Finset.univ.filter (fun i => 2 ≤ (S i ∩ H).card)).card := by simp
  rw [hits]
  omega

theorem two_high_per_row {n r : ℕ} (S : Fin r → Finset (Fin n)) (H : Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (low : ∀ p ∉ H, degree S p ≤ 2)
    (two : ∀ i, (S i ∩ H).card ≤ 2) (C : Circuit) (out : Fin r → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size := by
  have cost (i) : (S i \ H).card + min 2 (S i ∩ H).card = (S i).card := by
    rw [Nat.min_eq_right (two i),Finset.card_sdiff_add_card_inter]
  simpa only [cost] using two_high_points S H thin low C out hf hc

end PlaneResearch.ParameterOr
