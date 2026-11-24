import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1515_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate simplification follows the accepted restriction argument in L-meta-543.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval


private def monoGate (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private lemma simple_mono (g : Gate) (hm : monoGate g) (t : ℕ) (ls : List (Bool ⊕ ℕ)) :
    ∀ a ∈ (simplifyGate g.op t ls).1.toList, monoGate a := by
  intro a ha
  obtain ⟨hop, _⟩ := hm
  rcases hop with hop | hop <;> rw [hop] at ha <;>
    rcases ls with _ | ⟨u, _ | ⟨v, _ | ⟨z, l⟩⟩⟩ <;> (try cases u) <;> (try cases v) <;>
    simp_all [simplifyGate, simpAnd, simpOr, monoGate]

private lemma init_read (b i : ℕ) :
    ((List.range b).map (Sum.inr : ℕ → Bool ⊕ ℕ)).getD i (.inl false) =
      if i < b then .inr i else .inl false := by
  by_cases h : i < b
  · simp [List.getD, List.getElem?_eq_getElem, h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h), if_neg h]

private lemma preserve_early (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length)
    (w : List Bool) (i : ℕ) (hi : i < w.length + k) :
    (wiresFrom gs w).getD i false = (wiresFrom (gs.take k) w).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gs, wiresFrom_append]
  apply wiresFrom_getD_lt
  simpa [wiresFrom_length, Nat.min_eq_left hk] using hi

private lemma size_opt {α : Type*} (a : Option α) : a.toList.length ≤ 1 := by
  cases a <;> simp

private lemma take_one (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    gs.take (k+1) = gs.take k ++ [gs[k]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]
  simp

private def oldW {n : ℕ} (gs : List Gate) (k : ℕ) (x : Fin n → Bool) :=
  wiresFrom (gs.take k) (List.ofFn x)

private lemma oldW_next {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Fin n → Bool) :
    oldW gs (k+1) x = oldW gs k x ++ [gs[k].op.eval (gs[k].inputs.map fun i => (oldW gs k x).getD i false)] := by
  simp only [oldW, take_one gs k hk, wiresFrom_append]
  rfl

private def useSet (n j : ℕ) (gs : List Gate) (k : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => i.val < k ∧ j < i.val ∧ n+j ∈ (gs.get i).inputs

private lemma use_next (n j : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    (useSet n j gs (k+1)).card = (useSet n j gs k).card +
       if j < k ∧ n+j ∈ gs[k].inputs then 1 else 0 := by
  classical
  by_cases h : j < k ∧ n+j ∈ gs[k].inputs
  · have he : useSet n j gs (k+1) = insert ⟨k,hk⟩ (useSet n j gs k) := by
      ext i
      simp only [useSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hi,b⟩
        by_cases e : i.val = k
        · exact Or.inl (Fin.ext e)
        · exact Or.inr ⟨by omega,b⟩
      · rintro (rfl | ⟨hi,b⟩)
        · exact ⟨by simp,h⟩
        · exact ⟨by omega,b⟩
    rw [he, Finset.card_insert_of_notMem (by simp [useSet]), if_pos h]
  · have he : useSet n j gs (k+1) = useSet n j gs k := by
      ext i
      simp only [useSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi,b⟩
        refine ⟨?_,b⟩
        by_contra hn
        have eq : i = ⟨k,hk⟩ := Fin.ext (show i.val = k by omega)
        subst i
        exact h b
      · rintro ⟨hi,b⟩
        exact ⟨by omega,b⟩
    simp [he,h]

private def Domain {n : ℕ} (gs : List Gate) (h : ℕ) (x : Fin n → Bool) : Prop :=
  (wiresFrom gs (List.ofFn x)).getD (n+h) false = true

private def Certified (n : ℕ) (gs : List Gate) (h j k : ℕ)
    (a : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  a.1.length = n+k ∧ (∀ g ∈ a.2, monoGate g) ∧ gs.take h <+: a.2 ∧
  a.2.length + (useSet n j gs k).card + 1 + (if j < k then 1 else 0) ≤ k ∧
  a.1.getD (n+h) (.inl false) = .inl true ∧
  (j < k → a.1.getD (n+j) (.inl false) = .inl false) ∧
  ∀ x : Fin n → Bool, Domain gs h x → ElimInv n (List.ofFn x) (oldW gs k x) a

private lemma beginPass (n : ℕ) (gs : List Gate) (h j : ℕ) (hj : h < j) (hjlen : j < gs.length)
    (legal : ∀ g ∈ gs.take h, monoGate g) :
    ∃ a, Certified n gs h j (h+1) a := by
  let p := gs.take h
  let t := (List.range (n+h)).map (Sum.inr : ℕ → Bool ⊕ ℕ)
  have ht : t.length = n+h := by simp [t]
  have hp : p.length = h := by simp [p, Nat.min_eq_left (by omega : h ≤ gs.length)]
  have empty : useSet n j gs (h+1) = ∅ := by
    ext i
    simp only [useSet, Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    rintro ⟨hi,hi',_⟩
    omega
  refine ⟨(t ++ [.inl true],p), ?_⟩
  change (t ++ [Sum.inl true]).length = _ ∧ _
  refine ⟨by simp [ht, Nat.add_assoc], legal, ⟨[],by simp [p]⟩, ?_, ?_, ?_, ?_⟩
  · simp [empty,hp,show ¬j < h+1 by omega]
  · apply getD_snoc_eq
    omega
  · intro bad; omega
  intro x dom
  have oh : (oldW gs (h+1) x).length = n+(h+1) := by
    simp [oldW,wiresFrom_length,Nat.min_eq_left (by omega : h+1 ≤ gs.length)]
  refine ⟨by simp, by simp [oh,ht,Nat.add_assoc], ?_⟩
  intro i
  change statValid (n+p.length) ((t ++ [Sum.inl true]).getD i (Sum.inl false)) ∧
    statVal (wiresFrom p (List.ofFn x)) ((t ++ [Sum.inl true]).getD i (Sum.inl false)) = (oldW gs (h+1) x).getD i false
  by_cases eq : i = n+h
  · subst i
    rw [getD_snoc_eq _ _ _ _ ht.symm]
    have same := preserve_early gs (h+1) (by omega) (List.ofFn x) (n+h) (by simp)
    exact ⟨trivial, (same.symm.trans dom).symm⟩
  · rw [getD_snoc_ne _ _ _ _ (by omega)]
    dsimp only [t]
    rw [init_read]
    by_cases small : i < n+h
    · rw [if_pos small]
      refine ⟨by simpa [statValid,hp] using small, ?_⟩
      change (oldW gs h x).getD i false = _
      rw [oldW_next gs h (by omega)]
      apply Eq.symm
      apply getD_snoc_lt
      simpa [oldW,wiresFrom_length,Nat.min_eq_left (by omega : h ≤ gs.length)] using small
    · rw [if_neg small]
      exact ⟨trivial,(List.getD_eq_default _ _ (by omega)).symm⟩

private lemma extendPass (n : ℕ) (gs : List Gate) (h j k : ℕ) (hj : h < j) (hk : h < k)
    (kin : k < gs.length) (a : List (Bool ⊕ ℕ) × List Gate) (cert : Certified n gs h j k a)
    (leg : OkGate gs[k]) (other : k ≠ j → monoGate gs[k])
    (neg : k = j → gs[k].op = GateOp.not ∧ ∃ r : List ℕ, gs[k].inputs = (n+h)::r) :
    Certified n gs h j (k+1) (elimStep n a gs[k]) := by
  obtain ⟨len, mon, pref, size, mappedH, mappedJ, sem⟩ := cert
  let g := gs[k]
  let ins := g.inputs.map fun i => a.1.getD i (.inl false)
  let result := simplifyGate g.op (n+a.2.length) ins
  have atJ (eq : k = j) : result = (none,.inl false) := by
    obtain ⟨op,r,ls⟩ := neg eq
    change simplifyGate gs[k].op _ (gs[k].inputs.map _) = _
    rw [op,ls,List.map_cons,mappedH]
    rfl
  have touches (touch : j < k ∧ n+j ∈ gs[k].inputs) : result.1 = none := by
    apply simplifyGate_none_of_const _ _ _ leg.1 (by simpa [ins,g] using leg.2)
    · intro op
      obtain ⟨op' | op', _⟩ := other (by omega)
      all_goals simp_all [g]
    · refine ⟨false, List.mem_map.mpr ⟨n+j, touch.2, mappedJ touch.1⟩⟩
  have okNew : ∀ b ∈ result.1.toList, monoGate b := by
    by_cases eq : k = j
    · simp [atJ eq]
    · exact simple_mono g (other eq) _ _
  have spent : result.1.toList.length + (useSet n j gs (k+1)).card + 1 + (if j < k+1 then 1 else 0) + a.2.length ≤ k+1 := by
    rw [use_next _ _ _ _ kin]
    by_cases eq : k = j
    · rw [atJ eq]
      simp only [Option.toList_none,List.length_nil,zero_add]
      simp only [eq, Nat.lt_irrefl, false_and, ↓reduceIte, Nat.lt_add_one] at size ⊢
      omega
    · by_cases t : j < k ∧ n+j ∈ gs[k].inputs
      · rw [touches t, if_pos t]
        have jk := t.1
        simp only [Option.toList_none,List.length_nil,zero_add, if_pos jk, if_pos (by omega : j < k+1)] at size ⊢
        omega
      · rw [if_neg t]
        have b := size_opt result.1
        by_cases jk : j < k
        · simp only [if_pos jk, if_pos (by omega : j < k+1)] at size ⊢
          omega
        · simp only [if_neg jk, if_neg (by omega : ¬j < k+1)] at size ⊢
          omega
  change (a.1 ++ [result.2]).length = _ ∧ _
  refine ⟨by simp [len,Nat.add_assoc], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change z ∈ a.2 ++ result.1.toList at hz
    exact (List.mem_append.mp hz).elim (mon z) (okNew z)
  · exact pref.trans (List.prefix_append ..)
  · change (a.2 ++ result.1.toList).length + _ + _ + _ ≤ _
    rw [List.length_append]
    omega
  · change (a.1 ++ [result.2]).getD (n+h) _ = _
    rw [getD_snoc_ne _ _ _ _ (by omega), mappedH]
  · intro jlt
    change (a.1 ++ [result.2]).getD (n+j) _ = _
    by_cases eq : k = j
    · rw [getD_snoc_eq _ _ _ _ (by omega),atJ eq]
    · rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact mappedJ (by omega)
  · intro x dx
    rw [oldW_next gs k kin]
    exact elimInv_step _ _ _ _ _ leg (sem x dx)

end PEqualNP.Outside.L_meta_1515_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1515_aux

theorem PEqualNP.Outside.L_meta_1515 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  classical
  intro n m gs out j h legal neg unique hj jin nonconstant
  have hvj : h.val < j.val := hj
  have mono (i : Fin gs.length) (ne : i ≠ j) : monoGate (gs.get i) := by
    obtain ⟨op,sz⟩ := legal (gs.get i) (List.get_mem ..)
    refine ⟨?_,sz⟩
    rcases op with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (ne (unique i hn))
  have pres : ∀ g ∈ gs.take h.val, monoGate g := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have il : i < gs.length := by simp only [List.length_take] at hi; omega
    rw [List.getElem_take]
    exact mono ⟨i,il⟩ (fun eq => by have e := congrArg Fin.val eq; dsimp at e; simp only [List.length_take] at hi; omega)
  have run (k : ℕ) : h.val < k → k ≤ gs.length → ∃ a, Certified n gs h.val j.val k a := by
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk kl
      by_cases eq : k = h.val
      · subst k
        exact beginPass n gs _ _ hvj j.isLt pres
      have kin : k < gs.length := by omega
      obtain ⟨a,ha⟩ := ih (by omega) (by omega)
      refine ⟨_, extendPass n gs _ _ k hvj (by omega) kin a ha ?_ ?_ ?_⟩
      · exact legal _ (List.getElem_mem ..)
      · intro ne
        exact mono ⟨k,kin⟩ (fun e => ne (congrArg Fin.val e))
      · intro eq
        have e : (⟨k, kin⟩ : Fin gs.length) = j := Fin.ext eq
        change (gs.get ⟨k,kin⟩).op = GateOp.not ∧ ∃ r, (gs.get ⟨k,kin⟩).inputs = _ :: r
        rw [e]
        exact ⟨neg,jin⟩
  obtain ⟨a, _, good, pre, bound, _, _, semantics⟩ := run gs.length h.isLt le_rfl
  have agree (w : Fin m) (x : Fin n → Bool) (dx : Domain gs h.val x) :
      statVal (wiresFrom a.2 (List.ofFn x)) (a.1.getD (out w) (.inl false)) =
      (Circuit.mk gs (out w)).eval (List.ofFn x) := by
    simpa [oldW, Circuit.eval, Circuit.wires, wiresFrom] using ((semantics x dx).2.2 (out w)).2
  have actual (w : Fin m) : ∃ i : ℕ, a.1.getD (out w) (.inl false) = .inr i := by
    cases sel : a.1.getD (out w) (.inl false) with
    | inr i => exact ⟨i,rfl⟩
    | inl c =>
      obtain ⟨x,y,dx,dy,tx,fy⟩ := nonconstant w
      have xeq := agree w x dx
      have yeq := agree w y dy
      rw [sel,tx] at xeq
      rw [sel,fy] at yeq
      exact Bool.noConfusion (xeq.symm.trans yeq)
  choose out' hout using actual
  refine ⟨a.2,out',good,pre,?_,?_⟩
  · have es : useSet n j.val gs gs.length =
        Finset.univ.filter (fun i : Fin gs.length => j < i ∧ n+j.val ∈ (gs.get i).inputs) := by
      ext i
      simp only [useSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hit => ⟨i.isLt, hit⟩⟩
    rw [es,if_pos j.isLt] at bound
    omega
  · intro w x dx
    have b := agree w x dx
    rw [hout w] at b
    exact b
