import Research.UnrestrictedOr

/-!
  SPDX-License-Identifier: Apache-2.0
  The evaluator and gate elimination pass follow the project's L-meta-543, which credits
  L-meta-468. The new theorem projects an entire family through a single shared circuit.
-/
namespace PlaneResearch.Projection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- Gate simplification follows the restriction proof in L_meta_468.
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

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

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

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

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

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


/-- Fix one input and simultaneously preserve all nonconstant restricted outputs.
If at least one output depends on the input, the shared gate list loses a gate. -/
theorem project_outputs {m r : ℕ} (gs0 : List Gate) (out : Fin r → ℕ)
    (f : Fin r → (Fin m → Bool) → Bool) (v : Fin m) (b : Bool)
    (ok : FanInTwo ⟨gs0,0⟩)
    (eval : ∀ j x, (Circuit.mk gs0 (out j)).eval (List.ofFn x) = f j x)
    (dep : ∃ j x, f j (Function.update x v false) ≠ f j (Function.update x v true))
    (nonc : ∀ j, ∃ x y, f j (Function.update x v b) ≠ f j (Function.update y v b)) :
    ∃ (gs1 : List Gate) (out1 : Fin r → ℕ), gs1.length + 1 ≤ gs0.length ∧
      FanInTwo ⟨gs1,0⟩ ∧ ∀ j x,
        (Circuit.mk gs1 (out1 j)).eval (List.ofFn x) = f j (Function.update x v b) := by
  classical
  obtain ⟨j0,hdep⟩ := dep
  let C := Circuit.mk gs0 (out j0)
  let F := f j0
  have hok : ∀ g ∈ C.gates, OkGate g := ok
  have hev (x) : C.eval (List.ofFn x) = F x := eval j0 x
  have hnc := nonc j0
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]

  have hval (j : Fin r) (x : Fin m → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD (out j) (Sum.inl false)) =
        f j (Function.update x v b) := by
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 (out j)).2, hgs, wiresFrom_norm]
    exact eval j (Function.update x v b)
  have pos (j : Fin r) : ∃ k : ℕ, acc.1.getD (out j) (Sum.inl false) = Sum.inr k := by
    cases h : acc.1.getD (out j) (Sum.inl false) with
    | inr k => exact ⟨k,rfl⟩
    | inl c =>
      obtain ⟨x,y,ne⟩ := nonc j
      have a := hval j x
      have b := hval j y
      rw [h] at a b
      exact (ne (a.symm.trans b)).elim
  choose out1 hout using pos
  refine ⟨acc.2,out1,?_,elimPass_ok m gs _ (by simp),?_⟩
  · have eq : C.gates.length = gs0.length := rfl
    omega
  · intro j x
    have h := hval j x
    rw [hout j] at h
    exact h

end PlaneResearch.Projection

namespace PlaneResearch.Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sumRow {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ A, x p = true)

private lemma fix_zero {n : ℕ} (A : Finset (Fin n)) (v : Fin n) (x : Fin n → Bool) :
    sumRow A (Function.update x v false) = sumRow (A.erase v) x := by
  simp only [sumRow, decide_eq_decide]
  constructor
  · rintro ⟨p,mem,h⟩
    have diff : p ≠ v := by rintro rfl; simp at h
    exact ⟨p, Finset.mem_erase.mpr ⟨diff,mem⟩, by simpa [Function.update_of_ne diff] using h⟩
  · rintro ⟨p,mem,h⟩
    obtain ⟨diff,mem⟩ := Finset.mem_erase.mp mem
    exact ⟨p,mem,by simpa [Function.update_of_ne diff] using h⟩

/-- Drop all points in U at zero. Every dropped point saves one gate and the
construction uses the same resulting gate list for every retained row. -/
theorem project_or_rows {n m : ℕ} (U : Finset (Fin n)) (S : Fin m → Finset (Fin n))
    (touch : ∀ p ∈ U, ∃ i, p ∈ S i)
    (remain : ∀ i, (S i \ U).Nonempty)
    (gs : List Gate) (out : Fin m → ℕ) (ok : FanInTwo ⟨gs,0⟩)
    (eval : ∀ i x, (Circuit.mk gs (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    ∃ (gs' : List Gate) (out' : Fin m → ℕ), gs'.length + U.card ≤ gs.length ∧
      FanInTwo ⟨gs',0⟩ ∧ ∀ i x, (Circuit.mk gs' (out' i)).eval (List.ofFn x) = sumRow (S i \ U) x := by
  classical
  induction U using Finset.induction_on generalizing S gs out with
  | empty => exact ⟨gs,out,by simp,ok,by simpa using eval⟩
  | @insert v U fresh ih =>
    obtain ⟨j,mj⟩ := touch v (Finset.mem_insert_self ..)
    have dep : ∃ i x, sumRow (S i) (Function.update x v false) ≠
        sumRow (S i) (Function.update x v true) := by
      refine ⟨j,fun _ => false,?_⟩
      have a : sumRow (S j) (Function.update (fun _ => false) v false) = false := by
        rw [fix_zero]; simp [sumRow]
      have b : sumRow (S j) (Function.update (fun _ => false) v true) = true :=
        decide_eq_true ⟨v,mj,Function.update_self ..⟩
      rw [a,b]
      decide
    have sep (i : Fin m) : ∃ x y, sumRow (S i) (Function.update x v false) ≠
        sumRow (S i) (Function.update y v false) := by
      obtain ⟨p,hp⟩ := remain i
      obtain ⟨mem,hn⟩ := Finset.mem_sdiff.mp hp
      have ne : p ≠ v := by rintro rfl; exact hn (Finset.mem_insert_self ..)
      refine ⟨fun _ => false,fun _ => true,?_⟩
      rw [fix_zero,fix_zero]
      have a : sumRow ((S i).erase v) (fun _ => false) = false := by simp [sumRow]
      have b : sumRow ((S i).erase v) (fun _ => true) = true :=
        decide_eq_true ⟨p,Finset.mem_erase.mpr ⟨ne,mem⟩,rfl⟩
      simp [a,b]
    obtain ⟨mid,mo,small,mok,me⟩ := project_outputs gs out (fun i => sumRow (S i)) v false ok eval dep sep
    let S' (i : Fin m) := (S i).erase v
    have eq (i : Fin m) : S' i \ U = S i \ insert v U := by
      ext p
      simp [S',Finset.mem_sdiff]
      tauto
    have touch' (p) (hp : p ∈ U) : ∃ i, p ∈ S' i := by
      obtain ⟨i,mem⟩ := touch p (Finset.mem_insert_of_mem hp)
      exact ⟨i,Finset.mem_erase.mpr ⟨fun h => fresh (h ▸ hp),mem⟩⟩
    have rem' (i) : (S' i \ U).Nonempty := eq i ▸ remain i
    have ev' (i) (x) : (Circuit.mk mid (mo i)).eval (List.ofFn x) = sumRow (S' i) x :=
      (me i x).trans (fix_zero (S i) v x)
    obtain ⟨ret,ro,rs,rok,re⟩ := ih S' touch' rem' mid mo mok ev'
    refine ⟨ret,ro,?_,rok,fun i x => (re i x).trans (congrArg (fun A => sumRow A x) (eq i))⟩
    rw [Finset.card_insert_of_notMem fresh]
    omega

end PlaneResearch.Projection

namespace PlaneResearch.Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Circuit lower bound after any zero restriction which leaves at least two points in every row. -/
theorem restricted_lower {n m : ℕ} (U : Finset (Fin n)) (S : Fin m → Finset (Fin n))
    (touch : ∀ p ∈ U, ∃ i, p ∈ S i)
    (two : ∀ i, 2 ≤ (S i \ U).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    U.card + m + (Finset.univ.filter (fun i => 3 ≤ (S i \ U).card)).card ≤ C.size := by
  classical
  have non (i) : (S i \ U).Nonempty := Finset.card_pos.mp (by have := two i; omega)
  obtain ⟨gs,o,saved,ok,eval⟩ := project_or_rows U S touch non C.gates out hf hc
  let R (i : Fin m) := S i \ U
  have sparse (i j : Fin m) (ne : i ≠ j) : (R i ∩ R j).card ≤ 1 := by
    apply le_trans (Finset.card_le_card ?_) (thin i j ne)
    exact Finset.inter_subset_inter Finset.sdiff_subset Finset.sdiff_subset
  let D := Circuit.mk gs 0
  have correct (i) (x : Fin n → Bool) :
      (D.wires (List.ofFn x)).getD (o i) false = true ↔ ∃ p ∈ R i, x p = true := by
    change (Circuit.mk gs (o i)).eval (List.ofFn x) = true ↔ _
    rw [eval]
    simp [sumRow,R]
  have h := (PlaneResearch.TripleSystems.Unrestricted.unrestricted_rows n m R two sparse D o ok correct).1
  change m + (Finset.univ.filter (fun i => 3 ≤ (S i \ U).card)).card ≤ gs.length at h
  change _ ≤ C.gates.length
  omega

end PlaneResearch.Projection

namespace PlaneResearch.Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shared {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : Finset (Fin n) :=
  (S i).filter fun p => ∃ j, j ≠ i ∧ p ∈ S j

/-- Every row can have arbitrary size as long as at most three of its points
also occur in other rows. Interior negations are unrestricted. -/
theorem three_shared {n m : ℕ} (S : Fin m → Finset (Fin n)) (two : ∀ i, 2 ≤ (S i).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (few : ∀ i, (shared S i).card ≤ 3)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size := by
  classical
  have choose_core (i : Fin m) : ∃ B, shared S i ⊆ B ∧ B ⊆ S i ∧ B.card = min 3 (S i).card := by
    have subset : shared S i ⊆ S i := Finset.filter_subset ..
    exact Finset.exists_subsuperset_card_eq subset
      (le_min (few i) (Finset.card_le_card subset)) (min_le_right ..)
  choose R keep sub card using choose_core
  let E (i : Fin m) := S i \ R i
  let U := Finset.univ.biUnion E
  have exclusive (i j : Fin m) {p} (h : p ∈ E i) (sj : p ∈ S j) : j = i := by
    by_contra ne
    obtain ⟨si,no⟩ := Finset.mem_sdiff.mp h
    exact no (keep i (Finset.mem_filter.mpr ⟨si,j,ne,sj⟩))
  have residual (i) : S i \ U = R i := by
    ext p
    constructor
    · intro h
      obtain ⟨si,nu⟩ := Finset.mem_sdiff.mp h
      by_contra nr
      exact nu (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨si,nr⟩⟩)
    · intro ri
      refine Finset.mem_sdiff.mpr ⟨sub i ri,?_⟩
      intro inU
      obtain ⟨j,_,ej⟩ := Finset.mem_biUnion.mp inU
      have eq := exclusive j i ej (sub i ri)
      subst j
      exact (Finset.mem_sdiff.mp ej).2 ri
  have touch (p) (h : p ∈ U) : ∃ i, p ∈ S i := by
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨i,(Finset.mem_sdiff.mp hi).1⟩
  have rem (i) : 2 ≤ (S i \ U).card := by rw [residual,card]; exact le_min (by decide) (two i)
  have d : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint E := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro p pi pj
    exact ne (exclusive j i pj (Finset.mem_sdiff.mp pi).1)
  have count : U.card = ∑ i, ((S i).card - (R i).card) := by
    rw [show U = Finset.univ.biUnion E from rfl, Finset.card_biUnion d]
    exact Finset.sum_congr rfl (fun i _ => Finset.card_sdiff_of_subset (sub i))
  have unit (i : Fin m) : (S i).card-1 = ((S i).card-(R i).card+1) +
      (if 3 ≤ (R i).card then 1 else 0) := by
    rw [card]
    have := two i
    split <;> omega
  have cost : (∑ i, ((S i).card-1)) =
      U.card + m + (Finset.univ.filter (fun i => 3 ≤ (S i \ U).card)).card := by
    simp_rw [unit,residual]
    simp [count,Finset.sum_add_distrib,←Finset.sum_filter]
  exact cost ▸ restricted_lower U S touch rem thin C out hf hc

theorem shared_le {n m : ℕ} (S : Fin m → Finset (Fin n))
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (i : Fin m) :
    (shared S i).card ≤ m-1 := by
  classical
  have next (p : ↥(shared S i)) : ∃ j, j ≠ i ∧ p.val ∈ S j := (Finset.mem_filter.mp p.property).2
  choose j ne mem using next
  let rest := (Finset.univ : Finset (Fin m)).erase i
  let f (p : ↥(shared S i)) : ↥rest := ⟨j p,Finset.mem_erase.mpr ⟨ne p,Finset.mem_univ _⟩⟩
  have inj : Function.Injective f := by
    intro p q eq
    have same : j p = j q := congrArg Subtype.val eq
    apply Subtype.ext
    apply Finset.card_le_one.mp (thin i (j q) (ne q).symm)
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp p.property).1,same ▸ mem p⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp q.property).1,mem q⟩
  simpa [rest] using Fintype.card_le_of_injective f inj

/-- In particular, any linear family with at most four rows attains its
separate-tree minimum even against circuits with unlimited negations. -/
theorem four_rows {n m : ℕ} (small : m ≤ 4) (S : Fin m → Finset (Fin n))
    (two : ∀ i, 2 ≤ (S i).card) (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (S i) x) :
    (∑ i, ((S i).card-1)) ≤ C.size :=
  three_shared S two thin (fun i => by have := shared_le S thin i; omega) C out hf hc

end PlaneResearch.Projection

namespace PlaneResearch.Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Assign an old input either a constant or an input of the new circuit. -/
def assignInput {n m : ℕ} (σ : Fin n → Bool ⊕ Fin m) (x : Fin m → Bool) (i : Fin n) : Bool :=
  (σ i).elim id x

private def inputTable {n m : ℕ} (σ : Fin n → Bool ⊕ Fin m) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i => (σ i).map id Fin.val

private lemma startTable {n m : ℕ} (σ : Fin n → Bool ⊕ Fin m) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (assignInput σ x)) (inputTable σ, []) := by
  refine ⟨by simp,by simp [inputTable],?_⟩
  intro i
  by_cases hi : i < n
  · rw [show (inputTable σ).getD i (.inl false) = (σ ⟨i,hi⟩).map id Fin.val from
          ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
    cases e : σ ⟨i,hi⟩ with
    | inl b => simp [assignInput,e,statVal,statValid]
    | inr j => simp [assignInput,e,statVal,statValid,wiresFrom_nil,ofFn_getD_lt _ _ _ j.isLt]
  · rw [List.getD_eq_default _ _ (by simp [inputTable]; omega),List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩

/-- Substitution of constants and input aliases preserves all nonconstant outputs.
If some output can distinguish two old inputs agreeing at every unpinned position,
at least one gate disappears. No dependency on the aliases' assigned values is required
in those two test inputs. -/
theorem specialize_outputs {n m r : ℕ} (σ : Fin n → Bool ⊕ Fin m) (gs0 : List Gate)
    (out : Fin r → ℕ) (ok : FanInTwo ⟨gs0,0⟩)
    (nonc : ∀ j, ∃ x y, (Circuit.mk gs0 (out j)).eval (List.ofFn (assignInput σ x)) ≠
      (Circuit.mk gs0 (out j)).eval (List.ofFn (assignInput σ y))) :
    ∃ (gs1 : List Gate) (out1 : Fin r → ℕ), FanInTwo ⟨gs1,0⟩ ∧ gs1.length ≤ gs0.length ∧
      (∀ j x, (Circuit.mk gs1 (out1 j)).eval (List.ofFn x) =
          (Circuit.mk gs0 (out j)).eval (List.ofFn (assignInput σ x))) ∧
      ((∃ (j : Fin r) (u v : Fin n → Bool), (∀ i a, σ i = .inr a → u i = v i) ∧
        (Circuit.mk gs0 (out j)).eval (List.ofFn u) ≠ (Circuit.mk gs0 (out j)).eval (List.ofFn v)) →
        gs1.length + 1 ≤ gs0.length) := by
  classical
  let gs := gs0.map normGate
  let acc := elimPass m gs (inputTable σ, [])
  have allowed : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok h (ok h hh)
  have eval (j : Fin r) (x : Fin m → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD (out j) (.inl false)) =
        (Circuit.mk gs0 (out j)).eval (List.ofFn (assignInput σ x)) := by
    have inv := elimInv_pass m (List.ofFn x) gs _ (inputTable σ, [])
      (fun g hg => (allowed g hg).1) (startTable σ x)
    exact (inv.2.2 (out j)).2.trans (by rw [show gs = gs0.map normGate from rfl,wiresFrom_norm]; rfl)
  have ex (j : Fin r) : ∃ k, acc.1.getD (out j) (.inl false) = .inr k := by
    cases h : acc.1.getD (out j) (.inl false) with
    | inr k => exact ⟨k,rfl⟩
    | inl b =>
      obtain ⟨x,y,ne⟩ := nonc j
      have a := eval j x
      have c := eval j y
      rw [h] at a c
      exact (ne (a.symm.trans c)).elim
  choose out1 hout using ex
  refine ⟨acc.2,out1,elimPass_ok m gs _ (by simp),?_,?_,?_⟩
  · simpa [acc,gs] using elimPass_len m gs (inputTable σ,[])
  · intro j x
    have h := eval j x
    rw [hout] at h
    exact h
  · rintro ⟨j,u,v,same,ne⟩
    let P : Set ℕ := {i | ∃ h : i < n, ∃ b, σ ⟨i,h⟩ = .inl b}
    have outfree : out j ∉ P := by
      rintro ⟨ho,b,eq⟩
      have pin (x : Fin m → Bool) : (Circuit.mk gs0 (out j)).eval (List.ofFn (assignInput σ x)) = b := by
        change (wiresFrom gs0 _).getD (out j) false = b
        rw [wiresFrom_getD_lt _ _ _ (by simpa),ofFn_getD_lt _ _ _ ho]
        simp [assignInput,eq]
      obtain ⟨x,y,bad⟩ := nonc j
      exact bad ((pin x).trans (pin y).symm)
    have reads : ∃ g ∈ gs, ∃ i ∈ g.inputs, i ∈ P := by
      by_contra! no
      have eq (i : ℕ) (hi : i ∉ P) : (List.ofFn u).getD i false = (List.ofFn v).getD i false := by
        by_cases h : i < n
        · rw [ofFn_getD_lt _ _ _ h,ofFn_getD_lt _ _ _ h]
          cases e : σ ⟨i,h⟩ with
          | inl b => exact (hi ⟨h,b,e⟩).elim
          | inr a => exact same _ a e
        · simp [List.getD_eq_default,show n ≤ i by omega]
      have agrees := (wiresFrom_agree gs P (List.ofFn u) (List.ofFn v) (by simp)
        (fun i h => by obtain ⟨hi,_,_⟩ := h; simpa using hi) eq no).2 (out j) outfree
      rw [show gs = gs0.map normGate from rfl,wiresFrom_norm,wiresFrom_norm] at agrees
      exact ne agrees
    obtain ⟨g,hg,i,hi,lt,b,pin⟩ := reads
    have eq : (inputTable σ).getD i (.inl false) = .inl b := by
      rw [inputTable,ofFn_getD_lt _ _ _ lt,pin]
      rfl
    simpa [acc,gs] using elimPass_len_lt m i gs (inputTable σ,[]) allowed
      (by simp [inputTable]; exact lt) ⟨b,eq⟩ ⟨g,hg,hi⟩

end PlaneResearch.Projection
