/-
SPDX-License-Identifier: Apache-2.0
Wire semantics and the two-gate argument adapt the project's proof of L-meta-1042
(brilliant-hq/pequalnp-proofs, PR #2080), which credits the L-meta-907 wire lemmas.
This file extends the argument to arbitrary finite linear set systems, including pairs,
and counts the unique negation separately.
-/
import Mathlib
import PEqualNP.Defs

namespace PlaneResearch.TripleSystems

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj



class Geometry where
  n : ℕ
  m : ℕ
  members : Fin m → Finset (Fin n)
  pt : Fin m → Fin 3 → Fin n
  belongs : ∀ l c, pt l c ∈ members l
  first_two : ∀ l, pt l 0 ≠ pt l 1
  separate : ∀ (l k : Fin m) (c d : Fin 3), pt l c ≠ pt l d →
    pt l c ∈ members k → pt l d ∈ members k → l = k
  large : Fin m → Prop
  distinct : ∀ l, large l → Function.Injective (pt l)

variable [geom : Geometry]

abbrev Line := Fin geom.m
abbrev Input := Fin geom.n → Bool
abbrev Wire := Input → Bool
def point (l : Line) (c : Fin 3) : Fin geom.n := geom.pt l c

abbrev Inc (l : Line) (p : Fin geom.n) := p ∈ geom.members l

def hit (l : Line) (x : Input) := ∃ p ∈ geom.members l, x p = true

def single (p : Fin geom.n) : Input := fun k => decide (k = p)

def outside (l : Line) : Input := fun k => decide (¬ Inc l k)

lemma same_line : ∀ (l m : Line) (c d : Fin 3), point l c ≠ point l d →
    Inc m (point l c) → Inc m (point l d) → l = m := geom.separate

lemma hit_single (l : Line) (p : Fin geom.n) : hit l (single p) ↔ Inc l p := by
  simp [hit, single, Inc]

lemma hit_point (l : Line) (c : Fin 3) : hit l (single (point l c)) :=
  (hit_single _ _).2 (geom.belongs l c)

lemma miss (l : Line) : ¬ hit l (outside l) := by
  rintro ⟨p, hp, hc⟩
  exact (of_decide_eq_true hc) hp

def Low (l : Line) (f : Wire) := ∀ x, f x = true → hit l x
def High (l : Line) (f : Wire) := ∀ x, hit l x → f x = true
def Exact (l : Line) (f : Wire) := ∀ x, f x = true ↔ hit l x

def Good (l : Line) (f : Wire) :=
  (Low l f ∨ High l f) ∧
  (∃ c d : Fin 3, point l c ≠ point l d ∧ f (single (point l c)) = true ∧ f (single (point l d)) = true) ∧
  f (outside l) = false

lemma exact_good {l : Line} {f : Wire} (h : Exact l f) : Good l f :=
  ⟨Or.inl (fun x => (h x).1),
    ⟨0, 1, geom.first_two l, (h _).2 (hit_point _ _), (h _).2 (hit_point _ _)⟩,
    Bool.eq_false_iff.mpr (fun ht => miss l ((h _).1 ht))⟩

lemma unique_line {l m : Line} {f : Wire} (h : Good l f) (h' : Good m f) : l = m := by
  obtain ⟨_, ⟨c, d, hn, hc, hd⟩, hf⟩ := h
  rcases h'.1 with low | high
  · apply same_line l m c d hn
    · exact (hit_single _ _).1 (low _ hc)
    · exact (hit_single _ _).1 (low _ hd)
  · have inc (j : Fin 3) : Inc l (point m j) := by
      by_contra hh
      have ht := high (outside l) ⟨point m j, geom.belongs m j, by simpa [outside] using hh⟩
      simp [hf] at ht
    exact (same_line m l 0 1 (geom.first_two m) (inc _) (inc _)).symm

def Falls (f : Wire) := ∀ x y : Input, (∀ k, x k = true → y k = true) →
  f y = true → f x = true

lemma good_rises {l : Line} {f : Wire} (h : Good l f) : ¬ Falls f := by
  rintro hf
  obtain ⟨hl | hh, ⟨c, _, _, hc, _⟩, ho⟩ := h
  · have h0 := hf (fun _ => false) _ (by simp) hc
    obtain ⟨_, _, hn⟩ := hl _ h0
    contradiction
  · have h1 := hh (fun _ => true) ⟨point l 0, geom.belongs l 0, rfl⟩
    have ht := hf (outside l) (fun _ => true) (by simp) h1
    simp [ho] at ht

lemma good_or {l : Line} {u v : Wire} (hl : geom.large l)
    (he : Exact l (fun x => u x || v x)) : Good l u ∨ Good l v := by
  have lu : Low l u := fun x h => (he x).1 (by simp [h])
  have lv : Low l v := fun x h => (he x).1 (by simp [h])
  have fu : u (outside l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lu _ h))
  have fv : v (outside l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lv _ h))
  have cov (c : Fin 3) := (he _).2 (hit_point l c)
  simp only [Bool.or_eq_true] at cov
  have gu (c d : Fin 3) (hn : c ≠ d) (hc : u (single (point l c)) = true)
      (hd : u (single (point l d)) = true) : Good l u ∨ Good l v :=
    Or.inl ⟨Or.inl lu, ⟨c, d, fun e => hn (geom.distinct l hl e), hc, hd⟩, fu⟩
  have gv (c d : Fin 3) (hn : c ≠ d) (hc : v (single (point l c)) = true)
      (hd : v (single (point l d)) = true) : Good l u ∨ Good l v :=
    Or.inr ⟨Or.inl lv, ⟨c, d, fun e => hn (geom.distinct l hl e), hc, hd⟩, fv⟩
  rcases cov 0 with a | a <;> rcases cov 1 with b | b <;> rcases cov 2 with c | c
  all_goals first
    | exact gu 0 1 (by decide) a b
    | exact gu 0 2 (by decide) a c
    | exact gu 1 2 (by decide) b c
    | exact gv 0 1 (by decide) a b
    | exact gv 0 2 (by decide) a c
    | exact gv 1 2 (by decide) b c

lemma good_and {l : Line} {u v : Wire}
    (he : Exact l (fun x => u x && v x)) : Good l u ∨ Good l v := by
  have hh (x : Input) (h : hit l x) : u x = true ∧ v x = true := by
    have ht := (he x).2 h
    simpa only [Bool.and_eq_true] using ht
  have makeGood (f : Wire) (h : High l f) (hf : f (outside l) = false) : Good l f :=
    ⟨Or.inr h, ⟨0, 1, geom.first_two l, h _ (hit_point _ _), h _ (hit_point _ _)⟩, hf⟩
  cases hu : u (outside l) with
  | false => exact Or.inl (makeGood _ (fun x h => (hh x h).1) hu)
  | true =>
    apply Or.inr (makeGood _ (fun x h => (hh x h).2) _)
    apply Bool.eq_false_iff.mpr
    intro hv
    exact miss l ((he _).1 (by simp [hu, hv]))

def wire (gs : List Gate) (i : ℕ) (x : Input) :=
  (wiresFrom gs (List.ofFn x)).getD i false

def prior (gs : List Gate) (k i : ℕ) : Wire :=
  if i < geom.n + k then wire gs i else fun _ => false

lemma prior_apply (gs : List Gate) (k i : ℕ) (x : Input) :
    prior gs k i x = if i < geom.n+k then wire gs i x else false := by
  by_cases h : i < geom.n+k <;> simp [prior, h]

lemma wire_gate (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Input) :
    wire gs (geom.n+k) x = gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := by
  simpa only [prior_apply, wire, List.length_ofFn] using getD_wiresFrom_gate gs (List.ofFn x) k hk

lemma good_in_range {gs : List Gate} {i : ℕ} {l : Line} (h : Good l (wire gs i)) :
    geom.n ≤ i ∧ i < geom.n + gs.length := by
  obtain ⟨_, ⟨c, d, hn, hc, hd⟩, _⟩ := h
  constructor
  · by_contra! hi
    have inp (x : Input) : wire gs i x = x ⟨i, hi⟩ := by
      unfold wire
      rw [getD_wiresFrom_lt _ _ _ (by simpa)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] : i < (List.ofFn x).length), List.getElem_ofFn]
    rw [inp] at hc hd
    exact hn ((of_decide_eq_true hc).symm.trans (of_decide_eq_true hd))
  · by_contra! hi
    unfold wire at hc
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hi)] at hc
    contradiction

lemma from_prior {gs : List Gate} {k i : ℕ} {l : Line} (h : Good l (prior gs k i)) :
    ∃ j < geom.n+k, Good l (wire gs j) := by
  unfold prior at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · exact False.elim (good_rises h (fun _ _ _ ht => ht))


def OnlyOne (C : Circuit) := ∀ i j : Fin C.gates.length,
  (C.gates.get i).op = GateOp.not → (C.gates.get j).op = GateOp.not → i = j

lemma not_falls (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (k : ℕ) (hk : k < C.gates.length) (hop : C.gates[k].op = GateOp.not) :
    Falls (wire C.gates (geom.n+k)) := by
  have hm : ∀ g ∈ C.gates.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hik : i < k := by simp only [List.length_take] at hi; omega
    have hil : i < C.gates.length := by omega
    rw [List.getElem_take]
    have hg' := (hf C.gates[i] (List.getElem_mem hil)).1
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have he := hu ⟨i, hil⟩ ⟨k, hk⟩ h hop
      have he' : i = k := congrArg Fin.val he
      omega
  intro x y hxy
  have hle (i : ℕ) : prior C.gates k i x = true → prior C.gates k i y = true := by
    have hv (z : Input) : prior C.gates k i z =
        (wiresFrom (C.gates.take k) (List.ofFn z)).getD i false := by
      rw [getD_wiresFrom_take _ _ _ _ (by omega)]
      simp only [prior_apply, wire, List.length_ofFn]
    rw [hv, hv]
    apply wiresFrom_mono _ hm _ _ (by simp)
    intro t ht
    by_cases h : t < geom.n
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at ht ⊢
      simp only [List.getElem_ofFn] at ht ⊢
      exact hxy ⟨t,h⟩ ht
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      contradiction
  rw [wire_gate _ _ hk, wire_gate _ _ hk, hop]
  cases he : C.gates[k].inputs with
  | nil => simp [GateOp.eval]
  | cons i is =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true']
    exact fun hy => Bool.eq_false_iff.mpr (fun hx => by simpa [hy] using hle i hx)

lemma earlier (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (l : Line) (hl : geom.large l) (k : ℕ) (hk : k < C.gates.length) (he : Exact l (wire C.gates (geom.n+k))) :
    ∃ i < geom.n+k, Good l (wire C.gates i) := by
  let g := C.gates[k]
  have ha := hf g (List.getElem_mem hk)
  have leg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := ha.1
  have len := ha.2
  have eqn (x : Input) : wire C.gates (geom.n+k) x =
      g.op.eval (g.inputs.map (fun i => prior C.gates k i x)) := wire_gate _ _ _ _
  have bad (b : Bool) (h : ∀ x, wire C.gates (geom.n+k) x = b) : False := by
    apply good_rises (exact_good he)
    intro x y _ ht
    rwa [h x, ← h y]
  rcases leg with ha | ho | hn
  · cases hin : g.inputs with
    | nil => exact (bad true (by simp [eqn, hin, ha, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good
        intro x
        simpa [eqn, hin, ha, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact l (fun x => prior C.gates k i x && prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ha, GateOp.eval] using he x
        exact (good_and h).elim from_prior from_prior
  · cases hin : g.inputs with
    | nil => exact (bad false (by simp [eqn, hin, ho, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good
        intro x
        simpa [eqn, hin, ho, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact l (fun x => prior C.gates k i x || prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ho, GateOp.eval] using he x
        exact (good_or hl h).elim from_prior from_prior
  · exact (good_rises (exact_good he) (not_falls C hf hu k hk hn)).elim


private lemma locate {gs : List Gate} {l : Line} {o : ℕ} (h : Good l (wire gs o)) :
    ∃ j : Fin gs.length, geom.n + j.val = o := by
  obtain ⟨lo,hi⟩ := good_in_range h
  exact ⟨⟨o-geom.n, by omega⟩, by dsimp; omega⟩

private lemma pack (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (out : Line → ℕ) (he : ∀ l, Exact l (wire C.gates (out l))) :
    ∃ idx : Line ⊕ {l : Line // geom.large l} → Fin C.gates.length,
      Function.Injective idx ∧ ∀ q, ¬ Falls (wire C.gates (geom.n + (idx q).val)) := by
  classical
  choose last hlast using fun l => locate (exact_good (he l))
  have dest (l : Line) : Good l (wire C.gates (geom.n+(last l).val)) :=
    hlast l ▸ exact_good (he l)
  have aux (v : {l : Line // geom.large l}) : ∃ k : Fin C.gates.length,
      k.val < (last v.val).val ∧ Good v.val (wire C.gates (geom.n+k.val)) := by
    obtain ⟨p,hp,hg⟩ := earlier C hf hu v.val v.property (last v.val) (last v.val).isLt
      (hlast v.val ▸ he v.val)
    obtain ⟨k,hk⟩ := locate hg
    exact ⟨k, by omega, hk ▸ hg⟩
  choose prev ltprev goodprev using aux
  let idx := Sum.elim last prev
  let owner : Line ⊕ {l : Line // geom.large l} → Line := Sum.elim id Subtype.val
  have assigned (q) : Good (owner q) (wire C.gates (geom.n+(idx q).val)) := by
    cases q with
    | inl l => exact dest l
    | inr v => exact goodprev v
  have owners {u v} (e : idx u = idx v) : owner u = owner v := by
    have h := assigned u
    rw [e] at h
    exact unique_line h (assigned v)
  refine ⟨idx, ?_, fun q => good_rises (assigned q)⟩
  intro u v eq
  have same := owners eq
  cases u with
  | inl l =>
    cases v with
    | inl j => exact congrArg Sum.inl same
    | inr j =>
      change l = j.val at same
      subst l
      exact ((ltprev j).ne (congrArg Fin.val eq.symm)).elim
  | inr l =>
    cases v with
    | inl j =>
      change l.val = j at same
      subst j
      exact ((ltprev l).ne (congrArg Fin.val eq)).elim
    | inr j => exact congrArg Sum.inr (Subtype.ext same)

private lemma extra {A : Type} [Fintype A] {s : ℕ} (f : A → Fin s)
    (inj : Function.Injective f) (t : Fin s) (missed : ∀ a, f a ≠ t) : Fintype.card A + 1 ≤ s := by
  let all : Option A → Fin s := fun | none => t | some a => f a
  have h : Function.Injective all := by
    intro x y e
    cases x <;> cases y
    · rfl
    · exact (missed _ e.symm).elim
    · exact (missed _ e).elim
    · exact congrArg some (inj e)
  simpa using Fintype.card_le_of_injective all h

end PlaneResearch.TripleSystems

namespace PlaneResearch.TripleSystems

open PEqualNP.CircuitLowerBounds

/-- For a linear set system with rows of size at least two, charge one gate per row and
one additional gate per row of size at least three. A negation, when present, is extra. -/
theorem thin_mixed_rows (n m : ℕ) (S : Fin m → Finset (Fin n))
    (min_size : ∀ i, 2 ≤ (S i).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hu : OnlyOne C)
    (hc : ∀ i (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (out i) false = true ↔
                                  ∃ p ∈ S i, x p = true) :
    let b := m + (Finset.univ.filter (fun i => 3 ≤ (S i).card)).card
    b ≤ C.size ∧ ((∃ t : Fin C.gates.length, (C.gates.get t).op = .not) → b+1 ≤ C.size) := by
  classical
  have pts (i : Fin m) : ∃ f : Fin 3 → Fin n,
      (∀ j, f j ∈ S i) ∧ f 0 ≠ f 1 ∧ (3 ≤ (S i).card → Function.Injective f) := by
    by_cases big : 3 ≤ (S i).card
    · obtain ⟨e⟩ : Nonempty (Fin 3 ↪ ↥(S i)) := Function.Embedding.nonempty_of_card_le (by simpa)
      have hinj : Function.Injective (fun j => (e j).val) := Subtype.val_injective.comp e.injective
      exact ⟨_, fun j => (e j).property, fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj he),
        fun _ => hinj⟩
    · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (min_size i)
      refine ⟨fun j => if j = 1 then b else a, ?_, ?_, fun h => (big h).elim⟩
      · intro j
        by_cases hj : j = 1 <;> simp [hj, ha, hb]
      · simpa using hab
  choose pt mem first distinct using pts
  let g : Geometry := {
    n := n, m := m, members := S, pt := pt, belongs := mem, first_two := first
    large := fun i => 3 ≤ (S i).card, distinct := distinct
    separate := by
      intro i j a b hab ha hb
      by_contra ne
      apply hab
      exact Finset.card_le_one.mp (thin i j ne) _ (Finset.mem_inter.mpr ⟨mem i a, ha⟩)
        _ (Finset.mem_inter.mpr ⟨mem i b, hb⟩) }
  letI : Geometry := g
  have output (l : @Line g) : @Exact g l (@wire g C.gates (out l)) := hc l
  obtain ⟨idx, inj, rising⟩ := @pack g C hf hu out output
  have dom : Fintype.card (@Line g ⊕ {l : @Line g // g.large l}) =
      m + (Finset.univ.filter (fun i => 3 ≤ (S i).card)).card := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype]
    apply congrArg (m + ·)
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  constructor
  · simpa only [←dom, Fintype.card_fin, Circuit.size] using Fintype.card_le_of_injective idx inj
  · rintro ⟨t,ht⟩
    apply (dom ▸ extra idx inj t ?_)
    intro a e
    have hr := rising a
    rw [e] at hr
    exact hr (@not_falls g C hf hu t t.isLt ht)

end PlaneResearch.TripleSystems

namespace PlaneResearch.TripleSystems

open PEqualNP.CircuitLowerBounds

/-- With rows of size two or three, the lower bound is their separate OR-tree cost. -/
theorem rank_three (n m : ℕ) (S : Fin m → Finset (Fin n))
    (size : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ 3)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hu : OnlyOne C)
    (hc : ∀ i (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (out i) false = true ↔
                                  ∃ p ∈ S i, x p = true) :
    let total := ∑ i, ((S i).card - 1)
    total ≤ C.size ∧ ((∃ t : Fin C.gates.length, (C.gates.get t).op = .not) →
      total + 1 ≤ C.size) := by
  have cost : (∑ i, ((S i).card - 1)) = m + (Finset.univ.filter (fun i => 3 ≤ (S i).card)).card := by
    calc
      (∑ i, ((S i).card - 1)) = ∑ i, (1 + if 3 ≤ (S i).card then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have := size i
        split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter]
  dsimp only
  rw [cost]
  exact thin_mixed_rows n m S (fun i => (size i).1) thin C out hf hu hc

def puncturedRows : Fin 7 → Finset (Fin 6) :=
  ![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}]

/-- The seven lines of the Fano plane with one input deleted, in the desk's indexing. -/
theorem punctured_fano (C : Circuit) (out : Fin 7 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hu : OnlyOne C)
    (hc : ∀ i (x : Fin 6 → Bool), (C.wires (List.ofFn x)).getD (out i) false = true ↔
                                  ∃ p ∈ puncturedRows i, x p = true) :
    11 ≤ C.size ∧ ((∃ t : Fin C.gates.length, (C.gates.get t).op = .not) → 12 ≤ C.size) := by
  have h := thin_mixed_rows 6 7 puncturedRows (by decide +kernel) (by decide +kernel) C out hf hu hc
  have e : 7 + (Finset.univ.filter (fun i => 3 ≤ (puncturedRows i).card)).card = 11 := by decide +kernel
  simpa only [e] using h

end PlaneResearch.TripleSystems
