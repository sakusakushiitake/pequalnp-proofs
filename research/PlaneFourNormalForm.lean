import Mathlib
import PEqualNP.Defs

/-
SPDX-License-Identifier: Apache-2.0
Wire semantics and the two-gate argument adapt the project's proof of L-meta-1042
(brilliant-hq/pequalnp-proofs, PR #2080), which credits the L-meta-907 wire lemmas.
This file extends the argument to arbitrary finite linear set systems, including pairs,
and establishes a strict penalty whenever an unrestricted circuit contains a negation.
-/

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



end PlaneResearch.TripleSystems

namespace PlaneResearch.TripleSystems.Unrestricted

open PEqualNP.CircuitLowerBounds
open PlaneResearch.TripleSystems
variable [geom : Geometry]

private lemma first_neg_falls (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (k : ℕ) (hk : k < C.gates.length) (hop : C.gates[k].op = GateOp.not)
    (before : ∀ i : Fin C.gates.length, i.val < k → (C.gates.get i).op ≠ .not) :
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
    · exact (before ⟨i,hil⟩ hik h).elim
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

private lemma earlier_positive (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (l : Line) (hl : geom.large l) (k : ℕ) (hk : k < C.gates.length) (he : Exact l (wire C.gates (geom.n+k))) (positive : C.gates[k].op ≠ .not) :
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
  · exact (positive hn).elim


private lemma locate_pos {gs : List Gate} {l : Line} {o : ℕ} (h : Good l (wire gs o)) :
    ∃ j : Fin gs.length, geom.n + j.val = o := by
  obtain ⟨lo,hi⟩ := good_in_range h
  exact ⟨⟨o-geom.n, by omega⟩, by dsimp; omega⟩


def Opp (l : Line) (f : Wire) := ∀ x, f x = true ↔ ¬ hit l x

private lemma opp_falls {l : Line} {f : Wire} (h : Opp l f) : Falls f := by
  intro x y xy hy
  apply (h x).2
  rintro ⟨p,hp,hx⟩
  exact (h y).1 hy ⟨p,hp,xy p hx⟩

private lemma opp_unique {l k : Line} {f : Wire} (a : Opp l f) (b : Opp k f) : l = k := by
  have both (j : Fin 3) : Inc k (point l j) := by
    apply (hit_single _ _).mp
    by_contra h
    exact (a _).mp ((b _).mpr h) (hit_point l j)
  exact same_line l k 0 1 (geom.first_two l) (both 0) (both 1)

private lemma token_unique {l k : Line} {f : Wire} (a : Good l f ∨ Opp l f)
    (b : Good k f ∨ Opp k f) : l = k := by
  rcases a with a|a <;> rcases b with b|b
  · exact unique_line a b
  · exact (good_rises a (opp_falls b)).elim
  · exact (good_rises b (opp_falls a)).elim
  · exact opp_unique a b

private lemma locate_opp {gs : List Gate} {l : Line} {o : ℕ} (h : Opp l (wire gs o)) :
    ∃ j : Fin gs.length, geom.n+j.val=o := by
  let z : Input := fun _ => false
  have t : wire gs o z = true := (h z).2 (by simp [hit,z])
  have lo : geom.n ≤ o := by
    by_contra! small
    unfold wire at t
    rw [getD_wiresFrom_lt _ _ _ (by simpa),
        List.getD_eq_getElem _ _ (by simpa using small),List.getElem_ofFn] at t
    contradiction
  have hi : o < geom.n + gs.length := by
    by_contra! big
    unfold wire at t
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using big)] at t
    contradiction
  exact ⟨⟨o-geom.n,by omega⟩,by dsimp; omega⟩

private lemma neg_predecessor (C : Circuit) (k : Fin C.gates.length)
    (hop : (C.gates.get k).op = .not) (P : Input → Prop)
    (correct : ∀ x, wire C.gates (geom.n+k.val) x = true ↔ P x)
    (nonconstant : ∃ x, ¬ P x) :
    ∃ i < geom.n+k.val, ∀ x, wire C.gates i x = true ↔ ¬ P x := by
  obtain ⟨z,hz⟩ := nonconstant
  have op : C.gates[k.val].op = .not := hop
  cases ins : C.gates[k.val].inputs with
  | nil =>
    exact (hz ((correct z).mp (by simp [wire_gate _ _ k.isLt,op,ins,GateOp.eval]))).elim
  | cons i more =>
    by_cases hi : i < geom.n+k.val
    · refine ⟨i,hi,?_⟩
      intro x
      have e := correct x
      rw [wire_gate _ _ k.isLt] at e
      simp only [op,ins,List.map_cons,GateOp.eval,List.headD_cons,prior_apply,
        if_pos hi,Bool.not_eq_true'] at e
      cases h : wire C.gates i x <;> simp_all
    · exact (hz ((correct z).mp (by simp [wire_gate _ _ k.isLt,op,ins,GateOp.eval,prior_apply,hi]))).elim

private lemma pack_any (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (out : Line → ℕ) (he : ∀ l, Exact l (wire C.gates (out l))) :
    ∃ idx : Line ⊕ {l : Line // geom.large l} → Fin C.gates.length,
      Function.Injective idx ∧ ∀ q, (C.gates.get (idx q)).op = .not →
        ¬ Falls (wire C.gates (geom.n + (idx q).val)) := by
  classical
  have ex (l : Line) : ∃ o, Exact l (wire C.gates o) := ⟨out l,he l⟩
  let first (l : Line) := Nat.find (ex l)
  have yes (l : Line) : Exact l (wire C.gates (first l)) := Nat.find_spec (ex l)
  have no (l : Line) (i : ℕ) (lt : i < first l) : ¬ Exact l (wire C.gates i) := Nat.find_min (ex l) lt
  choose last hlast using fun l => locate_pos (exact_good (yes l))
  have dest (l : Line) : Good l (wire C.gates (geom.n+(last l).val)) := hlast l ▸ exact_good (yes l)
  have aux (v : {l : Line // geom.large l}) : ∃ k : Fin C.gates.length,
      k.val < (last v.val).val ∧
      (Good v.val (wire C.gates (geom.n+k.val)) ∨ Opp v.val (wire C.gates (geom.n+k.val))) ∧
      ((C.gates.get k).op = .not → ¬ Falls (wire C.gates (geom.n+k.val))) := by
    by_cases hop : (C.gates.get (last v.val)).op = .not
    · obtain ⟨p,hp,hopp⟩ := neg_predecessor C (last v.val) hop (hit v.val)
        (hlast v.val ▸ yes v.val) ⟨outside v.val,miss v.val⟩
      obtain ⟨k,hk⟩ := locate_opp hopp
      refine ⟨k,by omega,Or.inr (hk ▸ hopp),?_⟩
      intro bad
      obtain ⟨i,hi,hpos⟩ := neg_predecessor C k bad (fun x => ¬ hit v.val x) (hk ▸ hopp)
        ⟨single (point v.val 0),fun h => h (hit_point _ _)⟩
      have smaller : i < first v.val := by rw [←hlast v.val]; omega
      exact (no v.val i smaller (fun x => by simpa using hpos x)).elim
    · obtain ⟨p,hp,hg⟩ := earlier_positive C hf v.val v.property (last v.val) (last v.val).isLt
        (hlast v.val ▸ yes v.val) hop
      obtain ⟨k,hk⟩ := locate_pos hg
      exact ⟨k,by omega,Or.inl (hk ▸ hg),fun _ => good_rises (hk ▸ hg)⟩
  choose prev ltprev token safe using aux
  let idx := Sum.elim last prev
  let owner : Line ⊕ {l : Line // geom.large l} → Line := Sum.elim id Subtype.val
  have assigned (q) : Good (owner q) (wire C.gates (geom.n+(idx q).val)) ∨
      Opp (owner q) (wire C.gates (geom.n+(idx q).val)) := by
    cases q with
    | inl l => exact Or.inl (dest l)
    | inr v => exact token v
  have owners {u v} (e : idx u = idx v) : owner u = owner v := by
    have h := assigned u
    rw [e] at h
    exact token_unique h (assigned v)
  refine ⟨idx, ?_, ?_⟩
  · intro u v eq
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
  · intro q
    cases q with
    | inl l => exact fun _ => good_rises (dest l)
    | inr v => exact safe v
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


end PlaneResearch.TripleSystems.Unrestricted

namespace PlaneResearch.TripleSystems.Unrestricted

open PEqualNP.CircuitLowerBounds
open PlaneResearch.TripleSystems

/-- The number and placement of NOT gates are unrestricted. A circuit containing
any negation strictly exceeds the separate OR-tree optimum on rank-three systems. -/
theorem unrestricted_rows (n m : ℕ) (S : Fin m → Finset (Fin n))
    (min_size : ∀ i, 2 ≤ (S i).card)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
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
  obtain ⟨idx, inj, rising⟩ := @pack_any g C hf out output
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
    let negs := Finset.univ.filter (fun k : Fin C.gates.length => (C.gates.get k).op = GateOp.not)
    have nonempty : negs.Nonempty := ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
    let z := negs.min' nonempty
    have zn := (Finset.mem_filter.mp (negs.min'_mem nonempty)).2
    have before (i : Fin C.gates.length) (lt : i.val < z.val) : (C.gates.get i).op ≠ .not := by
      intro hn
      have le : z ≤ i := negs.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
      exact (Nat.not_lt_of_ge le) lt
    apply (dom ▸ extra idx inj z ?_)
    intro a e
    have na := rising a
    rw [e] at na
    exact na zn (@first_neg_falls g C hf z z.isLt zn before)

end PlaneResearch.TripleSystems.Unrestricted

namespace PlaneResearch.TripleSystems.Unrestricted

open PEqualNP.CircuitLowerBounds

/-- With rows of size two or three, the lower bound is their separate OR-tree cost. -/
theorem rank_three (n m : ℕ) (S : Fin m → Finset (Fin n))
    (size : ∀ i, 2 ≤ (S i).card ∧ (S i).card ≤ 3)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (out : Fin m → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
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
  exact unrestricted_rows n m S (fun i => (size i).1) thin C out hf hc

def puncturedRows : Fin 7 → Finset (Fin 6) :=
  ![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}]

/-- The seven lines of the Fano plane with one input deleted, in the desk's indexing. -/
theorem punctured_fano (C : Circuit) (out : Fin 7 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 6 → Bool), (C.wires (List.ofFn x)).getD (out i) false = true ↔
                                  ∃ p ∈ puncturedRows i, x p = true) :
    11 ≤ C.size ∧ ((∃ t : Fin C.gates.length, (C.gates.get t).op = .not) → 12 ≤ C.size) := by
  have h := unrestricted_rows 6 7 puncturedRows (by decide +kernel) (by decide +kernel) C out hf hc
  have e : 7 + (Finset.univ.filter (fun i => 3 ≤ (puncturedRows i).card)).card = 11 := by decide +kernel
  simpa only [e] using h


def fanoRows : Fin 7 → Finset (Fin 7) :=
  ![{0,1,3},{1,2,4},{2,3,5},{3,4,6},{0,4,5},{1,5,6},{0,2,6}]

/-- All seven line outputs on seven points, with any number of NOT gates. -/
theorem fano (C : Circuit) (out : Fin 7 → ℕ) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ i (x : Fin 7 → Bool), (C.wires (List.ofFn x)).getD (out i) false = true ↔
                                  ∃ p ∈ fanoRows i, x p = true) :
    14 ≤ C.size ∧ ((∃ t : Fin C.gates.length, (C.gates.get t).op = .not) → 15 ≤ C.size) := by
  have h := unrestricted_rows 7 7 fanoRows (by decide +kernel) (by decide +kernel) C out hf hc
  have e : 7 + (Finset.univ.filter (fun i => 3 ≤ (fanoRows i).card)).card = 14 := by decide +kernel
  simpa only [e] using h

end PlaneResearch.TripleSystems.Unrestricted

namespace PlaneResearch.StarOwners
open PEqualNP.CircuitLowerBounds PlaneResearch.TripleSystems

def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun i => decide (i=p)
def pair {n : ℕ} (p q : Fin n) : Fin n → Bool := fun i => decide (i=p ∨ i=q)
def W {n : ℕ} (C : Circuit) (i : ℕ) (x : Fin n → Bool) := (C.wires (List.ofFn x)).getD i false
def Link (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ k g, b=n+k ∧ C.gates[k]?=some g ∧ a ∈ g.inputs
def Owns {n : ℕ} (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  W C (n+t) (pair u v) = true ∧ ∀ t' g', C.gates[t']?=some g' → g'.op=.and →
    Relation.TransGen (Link n C) (n+t') (n+t) → W C (n+t') (pair u v) = false

lemma input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) : W C i.val x=x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i.val false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using i.isLt),List.getD_eq_getElem _ _ (by simpa using i.isLt),
    List.getElem_ofFn]

lemma gate {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (x : Fin n → Bool) :
    W C (n+k) x = (C.gates[k]).op.eval ((C.gates[k]).inputs.map (fun j => if j<n+k then W C j x else false)) := by
  simpa only [W,List.length_ofFn,Circuit.wires,wiresFrom] using getD_wiresFrom_gate C.gates (List.ofFn x) k hk

lemma or_on {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length)
    (ho : (C.gates[k]).op=.or) (x : Fin n → Bool) :
    W C (n+k) x = true ↔ ∃ j ∈ (C.gates[k]).inputs, j<n+k ∧ W C j x = true := by
  rw [gate C k hk,ho]
  simp only [GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
  constructor
  · rintro ⟨j,hj,on'⟩
    by_cases lt : j<n+k
    · exact ⟨j,hj,lt,by simpa [lt] using on'⟩
    · simp [lt] at on'
  · rintro ⟨j,hj,lt,on'⟩
    exact ⟨j,hj,by simp [lt,on']⟩

theorem support_or_and {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (i : ℕ) :
    W C i x=true → (∃ p, x p=true ∧ W C i (single p)=true) ∨
    ∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (n+k) x=true ∧
      (n+k=i ∨ Relation.TransGen (Link n C) (n+k) i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro h
      by_cases raw : i<n
      · let p : Fin n := ⟨i,raw⟩
        change W C p.val _=true at h
        exact Or.inl ⟨p,(input C p x) ▸ h,by change W C p.val (single p)=true; simp [input,single]⟩
      · by_cases valid : i<n+C.gates.length
        · let k := i-n
          have hk : k<C.gates.length := by dsimp [k]; omega
          have eq : i=n+k := by dsimp [k]; omega
          rcases ops C.gates[k] (List.getElem_mem ..) with a|o
          · exact Or.inr ⟨k,C.gates[k],List.getElem?_eq_getElem hk,a,eq ▸ h,Or.inl eq.symm⟩
          · rw [eq,or_on C k hk o] at h
            obtain ⟨j,hj,lt,val⟩ := h
            rcases ih j (by omega) val with ⟨p,hp,one⟩|⟨t,g,hg,op,on',reach⟩
            · left; refine ⟨p,hp,?_⟩; rw [eq,or_on C k hk o]; exact ⟨j,hj,lt,one⟩
            · have link : Link n C j i := ⟨by omega,k,C.gates[k],eq,List.getElem?_eq_getElem hk,hj⟩
              refine Or.inr ⟨t,g,hg,op,on',Or.inr ?_⟩
              rcases reach with rfl|path
              · exact .single link
              · exact .tail path link
        · change (wiresFrom C.gates (List.ofFn x)).getD i false=true at h
          rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using Nat.le_of_not_lt valid)] at h
          contradiction

theorem wire_sources {n : ℕ} (C : Circuit) (u v : Fin n)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (i : ℕ) :
    W C i (pair u v)=true → W C i (single u)=true ∨ W C i (single v)=true ∨
    ∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (n+k) (pair u v)=true ∧
      (n+k=i ∨ Relation.TransGen (Link n C) (n+k) i) := by
  intro on'
  rcases support_or_and C (pair u v) ops i on' with ⟨p,hp,one⟩|and
  · rcases (of_decide_eq_true hp : p=u ∨ p=v) with rfl|rfl
    · exact Or.inl one
    · exact Or.inr (Or.inl one)
  · exact Or.inr (Or.inr and)

private lemma some_active_and {n : ℕ} (C : Circuit) (u v : Fin n)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (on' : W C C.output (pair u v)=true) (off₁ : W C C.output (single u)=false)
    (off₂ : W C C.output (single v)=false) :
    ∃ k, ∃ g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (n+k) (pair u v)=true := by
  rcases wire_sources C u v ops C.output on' with a|b|⟨k,g,hg,op,live,_⟩
  · simp [off₁] at a
  · simp [off₂] at b
  · exact ⟨k,g,hg,op,live⟩

/-- Every positive edge input has an owning AND. Choosing the first AND true on
that input excludes every true AND ancestor, even outside the output cone. -/
theorem edge_has_owner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true))
    (u v : Fin n) (uv : G.Adj u v) :
    ∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ Owns C k u v := by
  classical
  have pos : W C C.output (pair u v)=true := (hc _).trans (decide_eq_true ⟨u,v,uv,by simp [pair],by simp [pair]⟩)
  have neg (p : Fin n) : W C C.output (single p)=false := by
    apply (hc _).trans
    apply decide_eq_false
    rintro ⟨a,b,ab,ha,hb⟩
    have ea : a=p := of_decide_eq_true ha
    have eb : b=p := of_decide_eq_true hb
    simpa [ea,eb] using ab
  let P (k : ℕ) := ∃ g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (n+k) (pair u v)=true
  have ex : ∃ k,P k := some_active_and C u v ops pos (neg u) (neg v)
  obtain ⟨g,atg,op,on'⟩ := Nat.find_spec ex
  refine ⟨Nat.find ex,g,atg,op,on',?_⟩
  intro k g' atg' op' path
  have inc {a b : ℕ} (p : Relation.TransGen (Link n C) a b) : a<b := by
    induction p with
    | single h => exact h.1
    | tail _ h ih => exact lt_trans ih h.1
  have early : k<Nat.find ex := by have := inc path; omega
  apply Bool.eq_false_iff.mpr
  intro live
  exact Nat.find_min ex early ⟨g',atg',op',live⟩

noncomputable def ands (C : Circuit) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter (fun t => (C.gates.get t).op=.and)

/-- Whenever every AND's owned edges share a center, these centers cover the
graph, so the number of AND gates bounds its vertex cover number. -/
theorem centers_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true))
    (star : ∀ k g, C.gates[k]?=some g → g.op=.and → ∃ c : Fin n,
      ∀ u v, G.Adj u v → Owns C k u v → u=c ∨ v=c) :
    ∃ S : Finset (Fin n), S.card ≤ (ands C).card ∧ ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
  classical
  have pick (t : ↥(ands C)) : ∃ c : Fin n, ∀ u v, G.Adj u v → Owns C t.val.val u v → u=c ∨ v=c :=
    star _ C.gates[t.val.val] (List.getElem?_eq_getElem t.val.isLt) (by simpa [ands] using t.property)
  choose center good using pick
  refine ⟨Finset.univ.image center,by simpa using Finset.card_image_le (s := Finset.univ) (f := center),?_⟩
  intro u v uv
  obtain ⟨k,g,hg,op,owns⟩ := edge_has_owner G C ops hc u v uv
  obtain ⟨hk,eq⟩ := List.getElem?_eq_some_iff.mp hg
  have ga : C.gates[k].op = .and := by rw [eq]; exact op
  let t : ↥(ands C) := ⟨⟨k,hk⟩,by simpa [ands] using ga⟩
  have member : center t ∈ Finset.univ.image center := Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩
  rcases good t u v uv owns with hu|hv
  · exact Or.inl (hu ▸ member)
  · exact Or.inr (hv ▸ member)

end PlaneResearch.StarOwners

namespace PlaneResearch.BicliqueStar

variable {V : Type*} [DecidableEq V]

def NoSquare (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d

theorem bipartite_is_star (G : SimpleGraph V) (hG : NoSquare G) (A B : Finset V)
    (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! h
  obtain ⟨a,ha,c,hc,hac⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b,hb,d,hd,hbd⟩ := Finset.one_lt_card.mp h.2
  exact (hG a b c d (cross _ ha _ hb) (cross _ hc _ hb).symm (cross _ hc _ hd)
    (cross _ ha _ hd).symm).elim hac hbd

theorem one_center (G : SimpleGraph V) (hG : NoSquare G) (A B : Finset V)
    (ha : A.Nonempty) (hb : B.Nonempty) (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ c : V, ∀ a ∈ A, ∀ b ∈ B, a = c ∨ b = c := by
  rcases bipartite_is_star G hG A B cross with size|size
  · obtain ⟨c,hc⟩ := ha
    exact ⟨c,fun _ hx _ _ => Or.inl (Finset.card_le_one.mp size _ hx _ hc)⟩
  · obtain ⟨c,hc⟩ := hb
    exact ⟨c,fun _ _ _ hx => Or.inr (Finset.card_le_one.mp size _ hx _ hc)⟩

theorem cover_by_centers {m : ℕ} (G : SimpleGraph V) (hG : NoSquare G)
    (A B : Fin m → Finset V) (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (cross : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, G.Adj a b)
    (cover : ∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) :
    ∃ T : Finset V, T.card ≤ m ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  classical
  choose c hc using fun i => one_center G hG (A i) (B i) (ha i) (hb i) (cross i)
  refine ⟨Finset.univ.image c,by simpa using Finset.card_image_le (s:=Finset.univ) (f:=c),?_⟩
  intro u v huv
  obtain ⟨i,h|h⟩ := cover u v huv
  · rcases hc i u h.1 v h.2 with e|e
    · exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  · rcases hc i v h.1 u h.2 with e|e
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    · exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)

theorem binary_cone_card (inputs gates outputs : Finset ℕ)
    (parents : ℕ → Finset ℕ) (arity : ∀ j ∈ gates, (parents j).card ≤ 2)
    (disjoint : Disjoint inputs gates)
    (uses : ∀ w ∈ inputs ∪ gates, w ∈ outputs ∨ ∃ j ∈ gates, w ∈ parents j) :
    inputs.card ≤ gates.card + outputs.card := by
  have sub : inputs ∪ gates ⊆ outputs ∪ gates.biUnion parents := by
    intro w hw
    exact Finset.mem_union.mpr ((uses w hw).imp_right (fun h => Finset.mem_biUnion.mpr h))
  have upper : (gates.biUnion parents).card ≤ ∑ j ∈ gates, (parents j).card :=
    Finset.card_biUnion_le
  have bound : (∑ j ∈ gates, (parents j).card) ≤ ∑ _j ∈ gates, 2 := Finset.sum_le_sum arity
  have all := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  rw [Finset.card_union_of_disjoint disjoint] at all
  simp at bound
  omega

end PlaneResearch.BicliqueStar

namespace PlaneResearch.StarOwners
open PEqualNP.CircuitLowerBounds PlaneResearch.TripleSystems PlaneResearch.BicliqueStar

lemma wire_mono {n : ℕ} (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (x y : Fin n → Bool) (le : ∀ p, x p=true → y p=true) (i : ℕ) : W C i x=true → W C i y=true := by
  apply wiresFrom_mono C.gates ops (List.ofFn x) (List.ofFn y) (by simp) _ i
  intro j
  by_cases hj : j<n
  · simpa only [List.getD_eq_getElem _ _ (show j<(List.ofFn x).length by simpa using hj),
      List.getD_eq_getElem _ _ (show j<(List.ofFn y).length by simpa using hj),List.getElem_ofFn] using le ⟨j,hj⟩
  · simp [hj]

private def prior {n : ℕ} (C : Circuit) (k j : ℕ) (x : Fin n → Bool) :=
  if j<n+k then W C j x else false

private lemma prior_mono {n : ℕ} (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (k j : ℕ) (x y : Fin n → Bool) (le : ∀ p, x p=true → y p=true) :
    prior C k j x=true → prior C k j y=true := by
  unfold prior
  split
  · exact wire_mono C ops x y le j
  · exact id

private lemma singleton_parent {n : ℕ} (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (k : ℕ) (hk : k<C.gates.length) (j : ℕ) (reads : j ∈ (C.gates[k]).inputs)
    (u v : Fin n) (own : Owns C k u v) (on' : prior C k j (pair u v)=true) :
    prior C k j (single u)=true ∨ prior C k j (single v)=true := by
  by_cases lt : j<n+k
  · simp only [prior,if_pos lt] at on' ⊢
    rcases wire_sources C u v ops j on' with a|b|⟨t,g,atg,op,live,reach⟩
    · exact Or.inl a
    · exact Or.inr b
    · have link : Link n C j (n+k) := ⟨lt,k,C.gates[k],rfl,List.getElem?_eq_getElem hk,reads⟩
      have path : Relation.TransGen (Link n C) (n+t) (n+k) := by
        rcases reach with rfl|path
        · exact .single link
        · exact .tail path link
      have off := own.2 t g atg op path
      simp [off] at live
  · simp [prior,lt] at on'

/-- Testing the gate on inputs containing at most two vertices already suffices.
In any square-free graph, an AND that owns an edge and is false on all nonedges
has a common endpoint for every edge that it owns. -/
theorem clean_owns_star {n : ℕ} (G : SimpleGraph (Fin n)) (noSquare : NoSquare G)
    (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (k : ℕ) (hk : k<C.gates.length) (op : (C.gates[k]).op=.and)
    (arity : (C.gates[k]).inputs.length ≤ 2)
    (clean : ∀ a b : Fin n, W C (n+k) (pair a b)=true → G.Adj a b)
    (live : ∃ u v : Fin n, G.Adj u v ∧ Owns C k u v) :
    ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns C k u v → u=c ∨ v=c := by
  classical
  obtain ⟨u₀,v₀,_,o₀⟩ := live
  have inputs : ∃ j l, j ∈ (C.gates[k]).inputs ∧ l ∈ (C.gates[k]).inputs ∧
      ∀ x : Fin n → Bool, W C (n+k) x = (prior C k j x && prior C k l x) := by
    cases ins : (C.gates[k]).inputs with
    | nil =>
      have loop := clean u₀ u₀ (by simp [gate C k hk,op,ins,GateOp.eval])
      exact (G.loopless.irrefl _ loop).elim
    | cons j xs =>
      cases xs with
      | nil => exact ⟨j,j,by simp,by simp,fun x => by simp [gate C k hk,op,ins,GateOp.eval,prior]⟩
      | cons l ys =>
        have tail : ys=[] := by simpa [ins] using arity
        subst ys
        exact ⟨j,l,by simp,by simp,fun x => by simp [gate C k hk,op,ins,GateOp.eval,prior]⟩
  obtain ⟨j,l,rj,rl,eval⟩ := inputs
  let S (a : ℕ) : Finset (Fin n) := Finset.univ.filter (fun p => prior C k a (single p)=true)
  have covers (u v : Fin n) (own : Owns C k u v) :
      (u ∈ S j ∨ v ∈ S j) ∧ (u ∈ S l ∨ v ∈ S l) := by
    have both := own.1
    rw [eval,Bool.and_eq_true_iff] at both
    simpa [S] using And.intro (singleton_parent C ops k hk j rj u v own both.1)
      (singleton_parent C ops k hk l rl u v own both.2)
  have cross (a : Fin n) (ha : a ∈ S j) (b : Fin n) (hb : b ∈ S l) : G.Adj a b := by
    apply clean
    rw [eval,Bool.and_eq_true_iff]
    refine ⟨prior_mono C ops k j (single a) (pair a b) ?_ (Finset.mem_filter.mp ha).2,
      prior_mono C ops k l (single b) (pair a b) ?_ (Finset.mem_filter.mp hb).2⟩
    · intro p hp
      exact decide_eq_true (Or.inl (of_decide_eq_true hp))
    · intro p hp
      exact decide_eq_true (Or.inr (of_decide_eq_true hp))
  have non (s : Finset (Fin n)) (h : u₀ ∈ s ∨ v₀ ∈ s) : s.Nonempty :=
    h.elim (fun a => ⟨_,a⟩) (fun b => ⟨_,b⟩)
  have base := covers u₀ v₀ o₀
  obtain ⟨c,star⟩ := one_center G noSquare (S j) (S l) (non _ base.1) (non _ base.2) cross
  refine ⟨c,fun u v _ own => ?_⟩
  obtain ⟨a|a,b|b⟩ := covers u v own
  · exact Or.inl ((star u a u b).elim id id)
  · exact star u a v b
  · exact (star v a u b).symm
  · exact Or.inr ((star v a v b).elim id id)

/-- To test whether all AND gates vanish on all independent inputs, it is
enough to test singletons and nonedge pairs. A first active AND has at most
two predecessors, and each active predecessor has a supporting singleton. -/
theorem pair_tests_suffice {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n)) (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (test : ∀ k g, C.gates[k]?=some g → g.op=.and →
      ∀ p q : Fin n, W C (n+k) (pair p q)=true → G.Adj p q)
    (s : ℕ) (g : Gate) (atg : C.gates[s]?=some g) (op : g.op=.and)
    (x : Fin n → Bool) (on' : W C (n+s) x=true) :
    ∃ p q, G.Adj p q ∧ x p=true ∧ x q=true := by
  classical
  let P (k : ℕ) := ∃ g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (n+k) x=true
  have exists' : ∃ k,P k := ⟨s,g,atg,op,on'⟩
  let k := Nat.find exists'
  obtain ⟨g₀,found,and₀,active⟩ := (Nat.find_spec exists' : P k)
  obtain ⟨hk,eq⟩ := List.getElem?_eq_some_iff.mp found
  have arg (j : ℕ) (live : prior C k j x=true) : ∃ p, x p=true ∧ prior C k j (single p)=true := by
    by_cases lt : j<n+k
    · simp only [prior,if_pos lt] at live ⊢
      rcases support_or_and C x ops j live with yes|⟨t,g',ht,and',active',reach⟩
      · exact yes
      · have early : t<k := by
          rcases reach with same|path
          · omega
          · have inc {a b : ℕ} (h : Relation.TransGen (Link n C) a b) : a<b := by
              induction h with
              | single a => exact a.1
              | tail _ h ih => exact lt_trans ih h.1
            have := inc path
            omega
        exact (Nat.find_min exists' early ⟨g',ht,and',active'⟩).elim
    · simp [prior,lt] at live
  have evaluate (y : Fin n → Bool) : W C (n+k) y = g₀.inputs.all (fun j => prior C k j y) := by
    have ek : C.gates[k]=g₀ := eq
    rw [gate C k hk,ek,and₀]
    simp [GateOp.eval,prior]
  have arity := two g₀ (List.mem_of_getElem? found)
  rw [evaluate] at active
  cases ins : g₀.inputs with
  | nil =>
    let p : Fin n := ⟨0,hn⟩
    have loop := test k g₀ found and₀ p p (by simp [evaluate,ins])
    exact (G.loopless.irrefl _ loop).elim
  | cons a tail =>
    have liveA : prior C k a x=true := List.all_eq_true.mp active a (by simp [ins])
    obtain ⟨p,xp,one⟩ := arg a liveA
    cases tail with
    | nil =>
      have lift : prior C k a (pair p p)=true :=
        prior_mono C ops k a (single p) (pair p p) (fun i h => decide_eq_true (Or.inl (of_decide_eq_true h))) one
      have loop := test k g₀ found and₀ p p (by simp [evaluate,ins,lift])
      exact (G.loopless.irrefl _ loop).elim
    | cons b rest =>
      have empty : rest=[] := by simpa [ins] using arity
      subst rest
      have liveB : prior C k b x=true := List.all_eq_true.mp active b (by simp [ins])
      obtain ⟨q,xq,other⟩ := arg b liveB
      have lp := prior_mono C ops k a (single p) (pair p q)
        (fun i h => decide_eq_true (Or.inl (of_decide_eq_true h))) one
      have lq := prior_mono C ops k b (single q) (pair p q)
        (fun i h => decide_eq_true (Or.inr (of_decide_eq_true h))) other
      exact ⟨p,q,test k g₀ found and₀ p q (by simp [evaluate,ins,lp,lq]),xp,xq⟩

theorem pair_tests_iff {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n)) (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ p q : Fin n, W C (n+k) (pair p q)=true → G.Adj p q) ↔
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ x : Fin n → Bool, W C (n+k) x=true →
      ∃ p q, G.Adj p q ∧ x p=true ∧ x q=true) := by
  constructor
  · exact pair_tests_suffice hn G C ops two
  · intro global k g atg op p q on'
    obtain ⟨a,b,ab,aa,bb⟩ := global k g atg op (pair p q) on'
    rcases (of_decide_eq_true aa : a=p ∨ a=q) with rfl|rfl <;>
      rcases (of_decide_eq_true bb : b=_ ∨ b=_) with e|e <;> subst b
    · exact (G.loopless.irrefl _ ab).elim
    · exact ab
    · exact ab.symm
    · exact (G.loopless.irrefl _ ab).elim

end PlaneResearch.StarOwners

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

abbrev Node (n : ℕ) (C : Circuit) := Fin (n+C.gates.length)
def node {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) : Node n C := ⟨n+k,by omega⟩
noncomputable def parents {n : ℕ} (C : Circuit) (w : Node n C) : Finset (Node n C) := by
  classical
  exact Finset.univ.filter (fun p => Link n C p.val w.val)
def support {n : ℕ} (C : Circuit) (w : Node n C) : Finset (Fin n) :=
  Finset.univ.filter (fun p => W C w.val (single p)=true)
noncomputable def live {n : ℕ} (C : Circuit) (out : Node n C) : Finset (Node n C) := by
  classical
  exact Finset.univ.filter (fun p => Relation.ReflTransGen (fun a b : Node n C => Link n C a.val b.val) p out)
abbrev NoSingletonAnd {n : ℕ} (C : Circuit) := ∀ k (hk : k<C.gates.length), (C.gates[k]).op=.and →
  ∀ p : Fin n, W C (n+k) (single p)=false

lemma mem_parents {n : ℕ} (C : Circuit) (w p : Node n C) :
    p ∈ parents C w ↔ Link n C p.val w.val := by classical simp [parents]

lemma gate_parent {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (p : Node n C) :
    p ∈ parents C (node C k hk) ↔ p.val<n+k ∧ p.val ∈ (C.gates[k]).inputs := by
  rw [mem_parents]
  constructor
  · rintro ⟨lt,j,g,eq,found,reads⟩
    change n+k=n+j at eq
    have jk : j=k := by omega
    subst j
    rw [List.getElem?_eq_getElem hk] at found
    cases found
    exact ⟨lt,reads⟩
  · rintro ⟨lt,reads⟩
    exact ⟨lt,k,C.gates[k],rfl,List.getElem?_eq_getElem hk,reads⟩

lemma capacity {n : ℕ} (C : Circuit) (two : ∀ g ∈ C.gates, g.inputs.length≤2) (w : Node n C) :
    (parents C w).card ≤ 2 := by
  by_cases raw : w.val<n
  · have emp : parents C w=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p h
      obtain ⟨_,j,_,eq,_,_⟩ := (mem_parents C w p).mp h
      omega
    simp [emp]
  · let k := w.val-n
    have hk : k<C.gates.length := by dsimp [k]; have := w.isLt; omega
    have eq : w=node C k hk := Fin.ext (by dsimp [node,k]; omega)
    rw [eq]
    have b : (parents C (node (n:=n) C k hk)).card ≤ (C.gates[k]).inputs.toFinset.card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro p hp
        exact List.mem_toFinset.mpr ((gate_parent C k hk p).mp hp).2
      · intro a _ b _ h; exact Fin.ext h
    exact b.trans ((List.toFinset_card_le _).trans (two _ (List.getElem_mem ..)))

lemma live_root {n : ℕ} (C : Circuit) (o : Node n C) : o ∈ live C o := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩

lemma live_parent {n : ℕ} (C : Circuit) (o w p : Node n C) (hw : w ∈ live C o)
    (hp : p ∈ parents C w) : p ∈ live C o := by
  classical
  have path := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.head ((mem_parents C w p).mp hp) path⟩

lemma has_reader {n : ℕ} (C : Circuit) (o w : Node n C) (hw : w ∈ live C o) :
    w=o ∨ ∃ j ∈ live C o, w ∈ parents C j := by
  classical
  rcases (Finset.mem_filter.mp hw).2.cases_head with eq|⟨j,link,path⟩
  · exact Or.inl eq
  · exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,path⟩,(mem_parents C j w).mpr link⟩

lemma raw_set {n : ℕ} (C : Circuit) (w : Node n C) (hi : w.val<n) :
    support C w = {⟨w.val,hi⟩} := by
  ext p
  let q : Fin n := ⟨w.val,hi⟩
  change p ∈ Finset.univ.filter (fun p => W C q.val (single p)=true) ↔ p ∈ ({q} : Finset (Fin n))
  simp [input,single,eq_comm]

lemma and_set {n : ℕ} (C : Circuit) (quiet : NoSingletonAnd (n:=n) C) (k : ℕ) (hk : k<C.gates.length)
    (and : (C.gates[k]).op=.and) : support C (node (n:=n) C k hk)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have yes := (Finset.mem_filter.mp hp).2
  change W C (n+k) (single p)=true at yes
  rw [quiet k hk and p] at yes
  contradiction

lemma or_set {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (op : (C.gates[k]).op=.or) :
    support C (node (n:=n) C k hk) = (parents C (node C k hk)).biUnion (support C) := by
  classical
  ext p
  change (p ∈ Finset.univ.filter (fun p => W C (n+k) (single p)=true)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,or_on C k hk op,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,hj,lt,on'⟩
    let v : Node n C := ⟨j,by omega⟩
    exact ⟨v,(gate_parent C k hk v).mpr ⟨lt,hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,on'⟩⟩
  · rintro ⟨v,hv,pv⟩
    have h := (gate_parent C k hk v).mp hv
    exact ⟨v.val,h.2,h.1,(Finset.mem_filter.mp pv).2⟩

noncomputable def family {n : ℕ} (C : Circuit) (out : Node n C) :=
  (live C out).image (support C)
noncomputable def forks {n : ℕ} (C : Circuit) (out : Node n C) : Finset (Node n C) := by
  classical
  exact (live C out).filter (fun w => n≤w.val ∧ (support C w).Nonempty ∧ ∀ p ∈ parents C w, (support C p).Nonempty)

/-- A set of at least two singleton responses first appears at an OR with
two nonempty, strictly smaller parent supports. -/
theorem first_union {n : ℕ} (C : Circuit) (out : Node n C) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (two : ∀ g ∈ C.gates, g.inputs.length≤2) (quiet : NoSingletonAnd (n:=n) C)
    (s : Finset (Fin n)) (made : s ∈ family C out) (big : 1<s.card) :
    (∃ w ∈ forks C out, support C w=s) ∧
    ∃ a ∈ family C out, ∃ b ∈ family C out, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s := by
  classical
  let F := (live C out).filter (fun w => support C w=s)
  obtain ⟨w₀,l₀,e₀⟩ := Finset.mem_image.mp made
  have non : F.Nonempty := ⟨w₀,Finset.mem_filter.mpr ⟨l₀,e₀⟩⟩
  obtain ⟨w,wf,minimal⟩ := Finset.exists_min_image F Fin.val non
  obtain ⟨lw,sw⟩ := Finset.mem_filter.mp wf
  have ng : n≤w.val := by
    by_contra! raw
    have card := congrArg Finset.card ((raw_set C w raw).symm.trans sw)
    simp at card
    omega
  let k := w.val-n
  have hk : k<C.gates.length := by dsimp [k]; have := w.isLt; omega
  have eq : w=node C k hk := Fin.ext (by dsimp [node,k]; omega)
  have union : (parents C w).biUnion (support C)=s := by
    rcases ops C.gates[k] (List.getElem_mem ..) with a|o
    · have emp : s=∅ := sw.symm.trans (eq ▸ and_set C quiet k hk a)
      simp [emp] at big
    · rw [eq,←or_set C k hk o,←eq,sw]
  have small (v : Node n C) (hv : v ∈ parents C w) : (support C v).card<s.card := by
    have sub : support C v ⊆ s := by
      rw [←union]
      exact Finset.subset_biUnion_of_mem (support C) hv
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => by
      have ge := minimal v (Finset.mem_filter.mpr ⟨live_parent C out w v lw hv,e⟩)
      have lt := ((mem_parents C w v).mp hv).1
      omega⟩)
  have cap := capacity C two w
  have twoP : (parents C w).card=2 := by
    by_contra ne
    have one : (parents C w).card≤1 := by omega
    rcases (parents C w).eq_empty_or_nonempty with empty|⟨v,hv⟩
    · simp [empty] at union; simp [←union] at big
    · have singleton : parents C w={v} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv,fun z hz => Finset.card_le_one.mp one _ hz _ hv⟩
      have h := small v hv
      simp [singleton] at union
      rw [union] at h
      exact (Nat.lt_irrefl _ h).elim
  obtain ⟨a,b,ab,pair⟩ := Finset.card_eq_two.mp twoP
  have pa : a ∈ parents C w := by simp [pair]
  have pb : b ∈ parents C w := by simp [pair]
  have combo : support C a ∪ support C b = s := by simpa [pair] using union
  have sa := small a pa
  have sb := small b pb
  have nonA : (support C a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.empty_union] at combo
    rw [combo] at sb
    exact Nat.lt_irrefl _ sb
  have nonB : (support C b).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.union_empty] at combo
    rw [combo] at sa
    exact Nat.lt_irrefl _ sa
  refine ⟨⟨w,Finset.mem_filter.mpr ⟨lw,ng,?_,?_⟩,sw⟩,
    support C a,Finset.mem_image_of_mem _ (live_parent C out w a lw pa),
    support C b,Finset.mem_image_of_mem _ (live_parent C out w b lw pb),sa,sb,combo⟩
  · rw [sw]; exact Finset.card_pos.mp (by omega)
  · intro p hp
    rw [pair] at hp
    rcases Finset.mem_insert.mp hp with rfl|h
    · exact nonA
    · exact Finset.mem_singleton.mp h ▸ nonB

end PlaneResearch.CleanWireModel

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

def Rect {n : ℕ} (C : Circuit) (w a b : Node n C) : Prop :=
  ∃ (k : ℕ) (hk : k<C.gates.length), w=node C k hk ∧ C.gates[k].op=.and ∧
    C.gates[k].inputs=[a.val,b.val] ∧ a.val<w.val ∧ b.val<w.val ∧
    (support C a).Nonempty ∧ (support C b).Nonempty

abbrev PairClean {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) := ∀ k (hk : k<C.gates.length),
  C.gates[k].op=.and → ∀ p q : Fin n, W C (n+k) (pair p q)=true → G.Adj p q

lemma quiet_of_clean {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (h : PairClean G C) :
    NoSingletonAnd (n:=n) C := by
  intro k hk op p
  apply Bool.eq_false_iff.mpr
  intro on'
  have eq : pair p p=single p := funext (fun i => by simp [pair,single])
  exact G.loopless.irrefl _ (h k hk op p p (eq ▸ on'))

lemma rect_unique {n : ℕ} (C : Circuit) {w a b e f : Node n C}
    (r : Rect C w a b) (s : Rect C w e f) : a=e ∧ b=f := by
  obtain ⟨k,hk,eq,_,ins,_⟩ := r
  obtain ⟨l,hl,eq',_,ins',_⟩ := s
  have ix := congrArg Fin.val (eq.symm.trans eq')
  change n+k=n+l at ix
  have kl := Nat.add_left_cancel ix
  subst l
  rw [ins] at ins'
  have vals := List.cons.inj ins'
  exact ⟨Fin.ext vals.1,Fin.ext (List.cons.inj vals.2).1⟩

lemma rect_parents {n : ℕ} (C : Circuit) {w a b : Node n C} (r : Rect C w a b) :
    parents C w = {a,b} := by
  classical
  obtain ⟨k,hk,rfl,_,ins,lt,lt',_⟩ := r
  ext p
  simp only [gate_parent,ins,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_,h|h⟩
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rintro (rfl|rfl)
    · exact ⟨lt,Or.inl rfl⟩
    · exact ⟨lt',Or.inr rfl⟩

lemma rect_cross {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (clean : PairClean G C)
    {w a b : Node n C} (r : Rect C w a b) {p q : Fin n}
    (ha : p ∈ support C a) (hb : q ∈ support C b) : G.Adj p q := by
  obtain ⟨k,hk,rfl,op,ins,lt,lt',_⟩ := r
  have va := wire_mono C ops (single p) (pair p q)
    (fun i h => decide_eq_true (Or.inl (of_decide_eq_true h))) a.val (Finset.mem_filter.mp ha).2
  have vb := wire_mono C ops (single q) (pair p q)
    (fun i h => decide_eq_true (Or.inr (of_decide_eq_true h))) b.val (Finset.mem_filter.mp hb).2
  change a.val<n+k at lt
  change b.val<n+k at lt'
  exact clean k hk op p q (by simp [gate C k hk,op,ins,GateOp.eval,lt,lt',va,vb])

/-- Take the first live wire which distinguishes a two-vertex input from
both singleton inputs. Its two parents witness opposite endpoints. -/
theorem edge_rect {n : ℕ} (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (u v : Fin n) (on' : W C o.val (pair u v)=true)
    (offU : W C o.val (single u)=false) (offV : W C o.val (single v)=false) :
    ∃ w ∈ live C o, ∃ a b, Rect C w a b ∧
      ((u ∈ support C a ∧ v ∈ support C b) ∨ (v ∈ support C a ∧ u ∈ support C b)) := by
  classical
  let D := (live C o).filter (fun w => W C w.val (pair u v)=true ∧
    W C w.val (single u)=false ∧ W C w.val (single v)=false)
  have ne : D.Nonempty := ⟨o,Finset.mem_filter.mpr ⟨live_root C o,on',offU,offV⟩⟩
  obtain ⟨w,hm,minimal⟩ := Finset.exists_min_image D Fin.val ne
  obtain ⟨lw,yes,noU,noV⟩ := Finset.mem_filter.mp hm
  have parent (p : Node n C) (pa : p ∈ parents C w) (onP : W C p.val (pair u v)=true) :
      W C p.val (single u)=true ∨ W C p.val (single v)=true := by
    by_contra! bad
    have le := minimal p (Finset.mem_filter.mpr ⟨live_parent C o w p lw pa,onP,
      Bool.eq_false_iff.mpr bad.1,Bool.eq_false_iff.mpr bad.2⟩)
    exact (Nat.not_le_of_gt ((mem_parents C w p).mp pa).1) le
  have ng : n≤w.val := by
    by_contra! raw
    let p : Fin n := ⟨w.val,raw⟩
    change W C p.val _=true at yes
    change W C p.val _=false at noU noV
    rw [input] at yes noU noV
    rcases (of_decide_eq_true yes : p=u ∨ p=v) with h|h
    · simp [single,h] at noU
    · simp [single,h] at noV
  let k := w.val-n
  have hk : k<C.gates.length := by dsimp [k]; have := w.isLt; omega
  have eq : w=node C k hk := Fin.ext (by dsimp [node,k]; omega)
  have eqw : w.val=n+k := congrArg Fin.val eq
  rw [eqw] at yes noU noV
  rcases ops C.gates[k] (List.getElem_mem ..) with and'|or'
  · have gateEq (x : Fin n → Bool) : W C (n+k) x =
        (C.gates[k]).inputs.all (fun i => if i<n+k then W C i x else false) := by
      simp [gate C k hk,and',GateOp.eval]
    have hp (j : ℕ) (hj : j ∈ C.gates[k].inputs) :
        ∃ p : Node n C, p.val=j ∧ j<n+k ∧
          (W C p.val (single u)=true ∨ W C p.val (single v)=true) := by
      have val := List.all_eq_true.mp ((gateEq _).symm ▸ yes) j hj
      by_cases lt : j<n+k
      · let p : Node n C := ⟨j,by omega⟩
        exact ⟨p,rfl,lt,parent p (eq ▸ (gate_parent C k hk p).mpr ⟨lt,hj⟩) (by simpa [lt] using val)⟩
      · simp [lt] at val
    cases ins : C.gates[k].inputs with
    | nil => simp [gateEq,ins] at noU
    | cons i tail =>
      obtain ⟨a,ai,la,sa⟩ := hp i (by simp [ins])
      have la' : a.val<n+k := by simpa [ai] using la
      cases tail with
      | nil =>
        rcases sa with s|s
        · simp [gateEq,ins,←ai,la',s] at noU
        · simp [gateEq,ins,←ai,la',s] at noV
      | cons j rest =>
        have arity := two C.gates[k] (List.getElem_mem ..)
        have emp : rest=[] := by simpa [ins] using arity
        subst rest
        obtain ⟨b,bj,lb,sb⟩ := hp j (by simp [ins])
        have lb' : b.val<n+k := by simpa [bj] using lb
        have mem (p : Fin n) (t : Node n C) (h : W C t.val (single p)=true) : p ∈ support C t :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        have both : (u ∈ support C a ∧ v ∈ support C b) ∨ (v ∈ support C a ∧ u ∈ support C b) := by
          rcases sa with x|x <;> rcases sb with y|y
          · simp [gateEq,ins,←ai,←bj,la',lb',x,y] at noU
          · exact Or.inl ⟨mem _ _ x,mem _ _ y⟩
          · exact Or.inr ⟨mem _ _ x,mem _ _ y⟩
          · simp [gateEq,ins,←ai,←bj,la',lb',x,y] at noV
        have ns : (support C a).Nonempty ∧ (support C b).Nonempty := by
          rcases both with ⟨x,y⟩|⟨x,y⟩ <;> exact ⟨⟨_,x⟩,⟨_,y⟩⟩
        exact ⟨w,lw,a,b,⟨k,hk,eq,and',by simpa [ai,bj] using ins,by rwa [ai,eqw],
          by rwa [bj,eqw],ns⟩,both⟩
  · obtain ⟨j,read,lt,pos⟩ := (or_on C k hk or' _).mp yes
    let p : Node n C := ⟨j,by omega⟩
    rcases parent p (eq ▸ (gate_parent C k hk p).mpr ⟨lt,read⟩) pos with h|h
    · have t := (or_on C k hk or' _).mpr ⟨j,read,lt,h⟩
      simp [noU] at t
    · have t := (or_on C k hk or' _).mpr ⟨j,read,lt,h⟩
      simp [noV] at t

end PlaneResearch.CleanWireModel

namespace PlaneResearch.StarCounting

/-- The union of the requested sets has at most one point per root and one
additional point per distinct nonsingleton set built by a binary union. -/
theorem multi_root_union {V : Type*} [DecidableEq V] (F R : Finset (Finset V)) (roots : R ⊆ F)
    (split : ∀ s ∈ F, 1<s.card → ∃ a ∈ F, ∃ b ∈ F, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    (R.biUnion id).card ≤ R.card + (F.filter (fun s => 1<s.card)).card := by
  classical
  suffices main : ∀ l (F R : Finset (Finset V)), F.card=l → R ⊆ F →
      (∀ s ∈ F, 1<s.card → ∃ a ∈ F, ∃ b ∈ F, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) →
      (R.biUnion id).card ≤ R.card + (F.filter (fun s => 1<s.card)).card from main _ F R rfl roots split
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro F R length roots split
    let D := F.filter (fun s => 1<s.card)
    by_cases any : D.Nonempty
    · obtain ⟨s,sd,maximal⟩ := Finset.exists_max_image D Finset.card any
      obtain ⟨sf,big⟩ := Finset.mem_filter.mp sd
      have less : (F.erase s).card<l := by rw [←length]; exact Finset.card_erase_lt_of_mem sf
      have still (t) (ht : t ∈ F.erase s) (sz : 1<t.card) :
          ∃ a ∈ F.erase s, ∃ b ∈ F.erase s, a.card<t.card ∧ b.card<t.card ∧ a ∪ b=t := by
        obtain ⟨_,tf⟩ := Finset.mem_erase.mp ht
        have bound := maximal t (Finset.mem_filter.mpr ⟨tf,sz⟩)
        obtain ⟨a,af,b,bf,ltA,ltB,eq⟩ := split t tf sz
        refine ⟨a,Finset.mem_erase.mpr ⟨?_,af⟩,b,Finset.mem_erase.mpr ⟨?_,bf⟩,ltA,ltB,eq⟩
        · rintro rfl; omega
        · rintro rfl; omega
      have deq : (F.erase s).filter (fun t => 1<t.card) = D.erase s := by ext; simp [D,and_assoc]
      have paid := Finset.card_erase_add_one sd
      change _ ≤ R.card+D.card
      by_cases sr : s ∈ R
      · obtain ⟨a,af,b,bf,ltA,ltB,union⟩ := split s sf big
        let Q := insert a (insert b (R.erase s))
        have inc : Q ⊆ F.erase s := by
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact Finset.mem_erase.mpr ⟨fun e => (Nat.ne_of_lt ltA) (congrArg Finset.card e),af⟩
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact Finset.mem_erase.mpr ⟨fun e => (Nat.ne_of_lt ltB) (congrArg Finset.card e),bf⟩
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1,roots (Finset.mem_erase.mp ht).2⟩
        have cover : R.biUnion id ⊆ Q.biUnion id := by
          intro x hx
          obtain ⟨t,tr,xt⟩ := Finset.mem_biUnion.mp hx
          by_cases eq : t=s
          · subst t
            change x ∈ s at xt
            rw [←union] at xt
            rcases Finset.mem_union.mp xt with ha|hb
            · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_insert_self ..,ha⟩
            · exact Finset.mem_biUnion.mpr ⟨b,by simp [Q],hb⟩
          · exact Finset.mem_biUnion.mpr ⟨t,by simp [Q,tr,eq],xt⟩
        have budget : Q.card ≤ R.card+1 := by
          have h₁ := Finset.card_insert_le a (insert b (R.erase s))
          have h₂ := Finset.card_insert_le b (R.erase s)
          have h₃ := Finset.card_erase_add_one sr
          change (insert a (insert b (R.erase s))).card ≤ _
          omega
        have h := ih _ less (F.erase s) Q rfl inc still
        rw [deq] at h
        have := Finset.card_le_card cover
        omega
      · have inc : R ⊆ F.erase s := fun t ht => Finset.mem_erase.mpr ⟨fun e => sr (e ▸ ht),roots ht⟩
        have h := ih _ less (F.erase s) R rfl inc still
        rw [deq] at h
        omega
    · have small (s : Finset V) (sr : s ∈ R) : s.card ≤ 1 := by
        by_contra! big
        exact any ⟨s,Finset.mem_filter.mpr ⟨roots sr,big⟩⟩
      have a : (R.biUnion id).card ≤ ∑ s ∈ R, s.card := Finset.card_biUnion_le
      have b : (∑ s ∈ R, s.card) ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum small
      simp at b
      omega

/-- Count reads leaving wires with empty singleton support. A productive AND
reads only positive-support wires. A gate returning to positive support has
room for at most one empty-support predecessor. -/
theorem zero_read_count {V : Type*} [DecidableEq V] (Z A M : Finset V) (roots : A ⊆ Z) (out : V) (parents : V → Finset V)
    (uses : ∀ i ∈ Z, i=out ∨ (∃ j ∈ Z \ A, i ∈ parents j) ∨ ∃ j ∈ M, i ∈ parents j)
    (binary : ∀ j ∈ Z \ A, (parents j ∩ Z).card ≤ 2)
    (mixed : ∀ j ∈ M, (parents j ∩ Z).card ≤ 1) : A.card ≤ (Z \ A).card + M.card + 1 := by
  let N (j : V) := parents j ∩ Z
  have cover : Z ⊆ ({out} ∪ (Z \ A).biUnion N) ∪ M.biUnion N := by
    intro i hi
    rcases uses i hi with rfl|⟨j,hj,h⟩|⟨j,hj,h⟩
    · simp
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨h,hi⟩⟩))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨h,hi⟩⟩)
  have a := Finset.card_le_card cover
  have b := Finset.card_union_le ({out} ∪ (Z \ A).biUnion N) (M.biUnion N)
  have c := Finset.card_union_le ({out} : Finset V) ((Z \ A).biUnion N)
  have z : ((Z \ A).biUnion N).card ≤ (Z \ A).card*2 := by
    apply Finset.card_biUnion_le.trans
    simpa using (Finset.sum_le_sum binary : (∑ i ∈ Z \ A, (parents i ∩ Z).card) ≤ ∑ _i ∈ Z \ A, 2)
  have m : (M.biUnion N).card ≤ M.card := by
    apply Finset.card_biUnion_le.trans
    simpa using (Finset.sum_le_sum mixed : (∑ i ∈ M, (parents i ∩ Z).card) ≤ ∑ _i ∈ M, 1)
  have eq := Finset.card_sdiff_add_card_eq_card roots
  simp only [Finset.card_singleton] at c
  omega

end PlaneResearch.StarCounting

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.StarCounting

noncomputable def zeros {n : ℕ} (C : Circuit) (o : Node n C) : Finset (Node n C) := by
  classical
  exact (live C o).filter (fun w => support C w=∅)
noncomputable def mixed {n : ℕ} (C : Circuit) (o : Node n C) : Finset (Node n C) := by
  classical
  exact (live C o).filter (fun w => (support C w).Nonempty ∧ ∃ p ∈ parents C w, support C p=∅)

private lemma mixed_capacity {n : ℕ} (C : Circuit) (o w : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (quiet : NoSingletonAnd (n:=n) C) (hw : w ∈ mixed C o) :
    (parents C w ∩ zeros C o).card≤1 := by
  classical
  obtain ⟨_,pos,p,hp,_⟩ := Finset.mem_filter.mp hw
  obtain ⟨_,k,g,eq,hg,_⟩ := (mem_parents C w p).mp hp
  obtain ⟨hk,geq⟩ := List.getElem?_eq_some_iff.mp hg
  have ew : w=node C k hk := Fin.ext eq
  have somePos : ∃ q ∈ parents C w, (support C q).Nonempty := by
    rcases ops C.gates[k] (List.getElem_mem ..) with a|b
    · rw [ew,and_set C quiet k hk a] at pos
      exact (Finset.not_nonempty_empty pos).elim
    · obtain ⟨v,hv⟩ := pos
      rw [ew,or_set C k hk b] at hv
      obtain ⟨q,parent,mem⟩ := Finset.mem_biUnion.mp hv
      exact ⟨q,ew ▸ parent,⟨v,mem⟩⟩
  obtain ⟨q,hq,positive⟩ := somePos
  have strict : parents C w ∩ zeros C o ⊂ parents C w := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left,?_⟩
    intro eq
    have inter : q ∈ parents C w ∩ zeros C o := by rw [eq]; exact hq
    have emp := (Finset.mem_filter.mp (Finset.mem_inter.mp inter).2).2
    exact positive.ne_empty emp
  have := Finset.card_lt_card strict
  have := capacity C two w
  omega

/-- Each distinguished empty-support root consumes one gate. All but at
most one force an additional gate distinct from the positive binary unions. -/
theorem gate_budget {n : ℕ} (C : Circuit) (o : Node n C) (A : Finset (Node n C))
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (quiet : NoSingletonAnd (n:=n) C)
    (root : A ⊆ zeros C o) (pos : ∀ w ∈ A, ∀ p ∈ parents C w, (support C p).Nonempty) :
    (forks C o).card + A.card + A.card ≤ C.gates.length + 1 := by
  classical
  let Z := zeros C o
  let M := mixed C o
  let B := forks C o
  have reader (w) (hw : w ∈ Z) :
      w=o ∨ (∃ j ∈ Z \ A, w ∈ parents C j) ∨ ∃ j ∈ M, w ∈ parents C j := by
    obtain ⟨lw,empty⟩ := Finset.mem_filter.mp hw
    rcases has_reader C o w lw with eq|⟨j,lj,hj⟩
    · exact Or.inl eq
    · by_cases z : support C j=∅
      · have nz : j ∉ A := fun ja => (pos j ja w hj).ne_empty empty
        exact Or.inr (Or.inl ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨lj,z⟩,nz⟩,hj⟩)
      · exact Or.inr (Or.inr ⟨j,Finset.mem_filter.mpr ⟨lj,Finset.nonempty_iff_ne_empty.mpr z,w,hj,empty⟩,hj⟩)
  have charge := zero_read_count Z A M root o (parents C) reader
    (fun j _ => (Finset.card_le_card Finset.inter_subset_left).trans (capacity C two j))
    (fun j h => mixed_capacity C o j ops two quiet h)
  have ZM : Disjoint Z M := Finset.disjoint_left.mpr (fun w hz hm =>
    (Finset.mem_filter.mp hm).2.1.ne_empty (Finset.mem_filter.mp hz).2)
  have ZMB : Disjoint (Z ∪ M) B := by
    apply Finset.disjoint_left.mpr
    intro w hm hb
    obtain ⟨_,_,live',all⟩ := Finset.mem_filter.mp hb
    rcases Finset.mem_union.mp hm with hz|hm
    · exact live'.ne_empty (Finset.mem_filter.mp hz).2
    · obtain ⟨_,_,p,hp,emp⟩ := Finset.mem_filter.mp hm
      exact (all p hp).ne_empty emp
  have gates (w) (hw : w ∈ (Z ∪ M) ∪ B) : n≤w.val := by
    rcases Finset.mem_union.mp hw with h|h
    · rcases Finset.mem_union.mp h with hz|hm
      · by_contra! raw
        have emp := (Finset.mem_filter.mp hz).2
        rw [raw_set C w raw] at emp
        simp at emp
      · obtain ⟨_,_,p,hp,_⟩ := Finset.mem_filter.mp hm
        obtain ⟨_,k,_,eq,_,_⟩ := (mem_parents C w p).mp hp
        omega
    · exact (Finset.mem_filter.mp h).2.1
  have bound : ((Z ∪ M) ∪ B).card ≤ (Finset.range C.gates.length).card := by
    apply Finset.card_le_card_of_injOn (fun w : Node n C => w.val-n)
    · intro w hw
      apply Finset.mem_range.mpr
      change w.val - n < C.gates.length
      have := w.isLt
      have := gates w hw
      omega
    · intro w hw v hv eq
      apply Fin.ext
      have := gates w hw
      have := gates v hv
      change w.val-n=v.val-n at eq
      omega
  rw [Finset.card_union_of_disjoint ZMB,Finset.card_union_of_disjoint ZM,Finset.card_range] at bound
  have total := Finset.card_sdiff_add_card_eq_card (show A ⊆ Z from root)
  change B.card+A.card+A.card ≤ _
  omega

end PlaneResearch.CleanWireModel

namespace PlaneResearch.StarCounting
open PlaneResearch.BicliqueStar

/-- A star cover of the edge set can use multiple roots for one center.
Each distinct nonsingleton union used by a center is counted once, and
square-freeness prevents two different centers from charging the same union. -/
theorem star_edges {V I : Type*} [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (sq : NoSquare G) (E : Finset (Sym2 V))
    (T : Finset I) (center : I → V) (leaves : I → Finset V) (U : Finset (Finset V))
    (root : ∀ t ∈ T, leaves t ∈ U) (adj : ∀ t ∈ T, ∀ p ∈ leaves t, G.Adj (center t) p)
    (edges : ∀ e ∈ E, ∃ t ∈ T, ∃ p ∈ leaves t, e=s(center t,p))
    (split : ∀ s ∈ U, 1<s.card → ∃ a ∈ U, ∃ b ∈ U, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    E.card ≤ T.card + (U.filter (fun s => 1<s.card)).card := by
  classical
  let K := T.image center
  let J (c : V) := T.filter (fun t => center t=c)
  let L (c : V) := (J c).image leaves
  let N (c : V) := (L c).biUnion id
  let F (c : V) := U.filter (fun s => ∀ p ∈ s, G.Adj c p)
  let D (c : V) := (F c).filter (fun s => 1<s.card)
  have estimate (c : V) : (N c).card ≤ (J c).card + (D c).card := by
    have inc : L c ⊆ F c := by
      intro s hs
      obtain ⟨t,j,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨ht,eq⟩ := Finset.mem_filter.mp j
      exact Finset.mem_filter.mpr ⟨root t ht,eq ▸ adj t ht⟩
    have pieces (s) (hs : s ∈ F c) (size : 1<s.card) : ∃ a ∈ F c, ∃ b ∈ F c,
        a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s := by
      obtain ⟨su,inside⟩ := Finset.mem_filter.mp hs
      obtain ⟨a,au,b,bu,ltA,ltB,eq⟩ := split s su size
      have aa : a ⊆ s := eq ▸ Finset.subset_union_left
      have bb : b ⊆ s := eq ▸ Finset.subset_union_right
      exact ⟨a,Finset.mem_filter.mpr ⟨au,fun p h => inside p (aa h)⟩,
        b,Finset.mem_filter.mpr ⟨bu,fun p h => inside p (bb h)⟩,ltA,ltB,eq⟩
    exact (multi_root_union (F c) (L c) inc pieces).trans
      (Nat.add_le_add_right (Finset.card_image_le (s := J c) (f := leaves)) _)
  have separate : (K : Set V).PairwiseDisjoint D := by
    intro c _ d _ ne
    apply Finset.disjoint_left.mpr
    intro s sc sd
    have ac := (Finset.mem_filter.mp (Finset.mem_filter.mp sc).1).2
    have ad := (Finset.mem_filter.mp (Finset.mem_filter.mp sd).1).2
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (Finset.mem_filter.mp sc).2
    exact (sq c a d b (ac a ha) (ad a ha).symm (ad b hb) (ac b hb).symm).elim ne ab
  have numD : (∑ c ∈ K, (D c).card) ≤ (U.filter (fun s => 1<s.card)).card := by
    rw [←Finset.card_biUnion separate]
    apply Finset.card_le_card
    intro s hs
    obtain ⟨c,_,sc⟩ := Finset.mem_biUnion.mp hs
    have h := Finset.mem_filter.mp sc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.1).1,h.2⟩
  have count : (∑ c ∈ K, (J c).card)=T.card := by
    exact (Finset.card_eq_sum_card_fiberwise (f := center) (s := T) (t := K)
      (fun t ht => Finset.mem_image_of_mem center ht)).symm
  let A (c : V) := (N c).image (fun p => s(c,p))
  have all : E ⊆ K.biUnion A := by
    intro e he
    obtain ⟨t,ht,p,hp,rfl⟩ := edges e he
    refine Finset.mem_biUnion.mpr ⟨center t,Finset.mem_image_of_mem _ ht,
      Finset.mem_image.mpr ⟨p,Finset.mem_biUnion.mpr ⟨leaves t,?_,hp⟩,rfl⟩⟩
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,rfl⟩,rfl⟩
  have upper : E.card ≤ ∑ c ∈ K, (N c).card :=
    (Finset.card_le_card all).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum
      (fun c _ => Finset.card_image_le (s := N c) (f := fun p => s(c,p)))))
  have add := Finset.sum_le_sum (s := K) (fun c _ => estimate c)
  rw [Finset.sum_add_distrib,count] at add
  omega

end PlaneResearch.StarCounting

namespace PlaneResearch.StarCounting
open PlaneResearch.BicliqueStar

/-- Count edges and cover vertices simultaneously when every edge lies in an
input rectangle whose two sides were formed from singleton supports. -/
theorem rectangle_counts {V I : Type*} [DecidableEq V] [DecidableEq I] [Nonempty V]
    (G : SimpleGraph V) (sq : NoSquare G) (E : Finset (Sym2 V)) (T : Finset I)
    (X Y : I → Finset V) (U : Finset (Finset V))
    (made : ∀ t ∈ T, X t ∈ U ∧ Y t ∈ U)
    (non : ∀ t ∈ T, (X t).Nonempty ∧ (Y t).Nonempty)
    (cross : ∀ t ∈ T, ∀ a ∈ X t, ∀ b ∈ Y t, G.Adj a b)
    (cover : ∀ e ∈ E, ∃ t ∈ T, ∃ a ∈ X t, ∃ b ∈ Y t, e=s(a,b))
    (split : ∀ s ∈ U, 1<s.card → ∃ a ∈ U, ∃ b ∈ U, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    E.card ≤ T.card+(U.filter (fun s => 1<s.card)).card ∧
    ∃ K : Finset V, K.card≤T.card ∧ ∀ e ∈ E, ∃ p ∈ K, p ∈ e := by
  classical
  have orient (t : I) : ∃ c : V, ∃ L : Finset V, t ∈ T →
      L ∈ U ∧ (∀ v ∈ L, G.Adj c v) ∧
      (∀ a ∈ X t, ∀ b ∈ Y t, ∃ p ∈ L, s(a,b)=s(c,p)) := by
    by_cases inT : t ∈ T
    · obtain ⟨x,xm⟩ := (non t inT).1
      obtain ⟨y,ym⟩ := (non t inT).2
      rcases bipartite_is_star G sq (X t) (Y t) (cross t inT) with small|small
      · refine ⟨x,Y t,fun _ => ⟨(made t inT).2,cross t inT x xm,?_⟩⟩
        intro a ha b hb
        have eq := Finset.card_le_one.mp small _ ha _ xm
        exact ⟨b,hb,by rw [eq]⟩
      · refine ⟨y,X t,fun _ => ⟨(made t inT).1,fun a ha => (cross t inT a ha y ym).symm,?_⟩⟩
        intro a ha b hb
        have eq := Finset.card_le_one.mp small _ hb _ ym
        exact ⟨a,ha,by rw [eq,Sym2.eq_swap]⟩
    · exact ⟨Classical.choice inferInstance,∅,fun ht => (inT ht).elim⟩
  choose center leaves h using orient
  have edge (e) (he : e ∈ E) : ∃ t ∈ T, ∃ p ∈ leaves t, e=s(center t,p) := by
    obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := cover e he
    exact ⟨t,ht,(h t ht).2.2 a ha b hb⟩
  refine ⟨star_edges G sq E T center leaves U (fun t ht => (h t ht).1) (fun t ht => (h t ht).2.1) edge split,
    T.image center,Finset.card_image_le,?_⟩
  intro e he
  obtain ⟨t,ht,p,_,rfl⟩ := edge e he
  exact ⟨center t,Finset.mem_image_of_mem _ ht,by simp⟩

end PlaneResearch.StarCounting

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.StarCounting PlaneResearch.BicliqueStar

/-- The square-free graph bounding the AND responses can differ from the
graph of edges used for the output lower bound. -/
theorem ambient_lower {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) (sq : NoSquare H) (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean H C) (off : ∀ p : Fin n, W C o.val (single p)=false)
    (on' : ∀ u v, G.Adj u v → W C o.val (pair u v)=true) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card+K.card≤C.gates.length+1 := by
  classical
  let A := (live C o).filter (fun w => ∃ a b, Rect C w a b)
  have pick (w : Node n C) : ∃ a b : Node n C, w ∈ A → Rect C w a b := by
    by_cases h : w ∈ A
    · obtain ⟨a,b,r⟩ := (Finset.mem_filter.mp h).2
      exact ⟨a,b,fun _ => r⟩
    · exact ⟨o,o,fun z => (h z).elim⟩
  choose x y spec using pick
  let X (w : Node n C) := support C (x w)
  let Y (w : Node n C) := support C (y w)
  have positive (w) (h : w ∈ A) : (X w).Nonempty ∧ (Y w).Nonempty := by
    obtain ⟨_,_,_,_,_,_,_,t⟩ := spec w h
    exact t
  have made (w) (h : w ∈ A) : X w ∈ family C o ∧ Y w ∈ family C o := by
    have pa := rect_parents C (spec w h)
    have lw := (Finset.mem_filter.mp h).1
    exact ⟨Finset.mem_image_of_mem _ (live_parent C o w (x w) lw (by simp [pa])),
      Finset.mem_image_of_mem _ (live_parent C o w (y w) lw (by simp [pa]))⟩
  have cover (e : Sym2 (Fin n)) (h : e ∈ G.edgeFinset) :
      ∃ t ∈ A, ∃ a ∈ X t, ∃ b ∈ Y t, e=s(a,b) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp h
      obtain ⟨t,lt,a,b,r,hits⟩ := edge_rect C o ops two u v (on' u v adj) (off u) (off v)
      have ht : t ∈ A := Finset.mem_filter.mpr ⟨lt,a,b,r⟩
      obtain ⟨ex,ey⟩ := rect_unique C r (spec t ht)
      subst a; subst b
      rcases hits with ⟨ha,hb⟩|⟨ha,hb⟩
      · exact ⟨t,ht,u,ha,v,hb,rfl⟩
      · exact ⟨t,ht,v,ha,u,hb,Sym2.eq_swap⟩
  have quiet := quiet_of_clean H C clean
  have split := first_union C o ops two quiet
  obtain ⟨m,K,small,meets⟩ := rectangle_counts H sq G.edgeFinset A X Y (family C o)
    made positive (fun t ht _ ha _ hb => rect_cross H C ops clean (spec t ht) ha hb) cover
    (fun s hs big => (split s hs big).2)
  have sub : ((family C o).filter (fun s => 1<s.card)) ⊆ (forks C o).image (support C) := by
    intro s hs
    obtain ⟨made,big⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_image.mpr (split s made big).1
  have b := (Finset.card_le_card sub).trans Finset.card_image_le
  have root : A ⊆ zeros C o := by
    intro w hw
    obtain ⟨k,hk,eq,ga,_⟩ := spec w hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,eq ▸ and_set C quiet k hk ga⟩
  have budget := gate_budget C o A ops two quiet root (by
    intro w hw p hp
    rw [rect_parents C (spec w hw)] at hp
    rcases Finset.mem_insert.mp hp with h|h
    · exact h ▸ (positive w hw).1
    · exact Finset.mem_singleton.mp h ▸ (positive w hw).2)
  refine ⟨K,?_,by omega⟩
  intro u v uv
  obtain ⟨p,hp,h⟩ := meets s(u,v) (SimpleGraph.mem_edgeFinset.mpr uv)
  rcases Sym2.mem_iff.mp h with rfl|rfl
  · exact Or.inl hp
  · exact Or.inr hp

/-- If every AND is false on singleton and nonedge tests for a square-free
graph, its output edge set and a vertex cover together cost at most g+1. -/
theorem clean_lower {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoSquare G) (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean G C) (off : ∀ p : Fin n, W C o.val (single p)=false)
    (on' : ∀ u v, G.Adj u v → W C o.val (pair u v)=true) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card+K.card≤C.gates.length+1 :=
  ambient_lower G G sq C o ops two clean off on'

end PlaneResearch.CleanWireModel

namespace PlaneResearch.ConditionalGraphLower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.StarOwners
open PlaneResearch.BicliqueStar PlaneResearch.CleanWireModel PlaneResearch.TripleSystems

/-- The edge-count plus cover lower bound with the additional independent
pair condition on AND gates. The circuit operations, graph cover predicate,
and edge cardinality are the ones used in the posted general problem. -/
theorem bound {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (non : ∃ u v, G.Adj u v)
    (square : ∀ a b c d : Fin n, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a)
    (covers : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t≤S.card)
    (mono : Monotone2 C) (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔
      ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) (clean : PairClean G C) :
    G.edgeSet.ncard+t≤C.size+1 := by
  classical
  obtain ⟨u,v,uv⟩ := non
  letI : Nonempty (Fin n) := ⟨u⟩
  have sq : NoSquare G := by
    intro a b c d ab bc cd da
    by_cases same : a=c
    · exact Or.inl same
    · right
      by_contra bd
      exact square a b c d ab.ne same da.ne.symm bc.ne bd cd.ne ab bc cd da
  have off (p : Fin n) : W C C.output (single p)=false := by
    apply Bool.eq_false_iff.mpr
    intro on'
    obtain ⟨a,b,h,aa,bb⟩ := (correct _).mp on'
    have ea : a=p := of_decide_eq_true aa
    have eb : b=p := of_decide_eq_true bb
    exact G.loopless.irrefl p (by simpa only [ea,eb] using h)
  have on' (p q : Fin n) (h : G.Adj p q) : W C C.output (pair p q)=true :=
    (correct _).mpr ⟨p,q,h,by simp [pair],by simp [pair]⟩
  have valid : C.output<n+C.gates.length := by
    by_contra! out
    have yes := on' u v uv
    change (wiresFrom C.gates (List.ofFn (pair u v))).getD C.output false=true at yes
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using out)] at yes
    contradiction
  let o : Node n C := ⟨C.output,valid⟩
  obtain ⟨K,hK,price⟩ := clean_lower G sq C o
    (fun g h => by simpa using (mono g h).1) (fun g h => (mono g h).2) clean off on'
  have count : G.edgeSet.ncard=G.edgeFinset.card := by
    rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have cover := covers K hK
  change G.edgeSet.ncard+t≤C.gates.length+1
  omega

end PlaneResearch.ConditionalGraphLower

namespace PlaneResearch.RelabelWires
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.TripleSystems

def index {n : ℕ} (σ : Fin n → Fin n) (i : ℕ) : ℕ := if hi : i<n then (σ ⟨i,hi⟩).val else i
def gateMap {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (index σ)⟩
def rename {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gateMap σ),index σ C.output⟩

theorem size_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : (rename σ C).size=C.size := by
  simp [rename,Circuit.size]

private lemma before {n : ℕ} (σ : Fin n → Fin n) (i k : ℕ) : index σ i<n+k ↔ i<n+k := by
  by_cases h : i<n
  · simp only [index,dif_pos h]
    have := (σ ⟨i,h⟩).isLt
    omega
  · simp [index,h]

/-- Relabel raw inputs while keeping every gate and its operation, even in
circuits with repeated or out-of-range predecessor references. -/
theorem wire {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    W (rename σ C) (index σ i) x = W C i (fun p => x (σ p)) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases raw : i<n
    · let p : Fin n := ⟨i,raw⟩
      change W (rename σ C) (index σ p.val) x = W C p.val _
      rw [show index σ p.val=(σ p).val from dif_pos raw,input,input]
    · rw [show index σ i=i from dif_neg raw]
      by_cases valid : i<n+C.gates.length
      · let k := i-n
        have hk : k<C.gates.length := by dsimp [k]; omega
        have hk' : k<(rename σ C).gates.length := by simpa [rename] using hk
        have eq : i=n+k := by dsimp [k]; omega
        rw [eq,gate (rename σ C) k hk',gate C k hk]
        simp only [rename,List.getElem_map,gateMap,List.map_map,Function.comp_apply]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases prev : j<n+k
        · simp only [Function.comp_apply,if_pos ((before σ j k).mpr prev),if_pos prev]
          simpa only [rename] using ih j (by omega)
        · simp [show ¬index σ j<n+k from fun h => prev ((before σ j k).mp h),prev]
      · change (wiresFrom (rename σ C).gates (List.ofFn x)).getD i false =
          (wiresFrom C.gates (List.ofFn (fun p => x (σ p)))).getD i false
        have outside : n + C.gates.length ≤ i := Nat.le_of_not_lt valid
        rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom,rename] using outside),
          List.getD_eq_default _ _ (by simpa [length_wiresFrom] using outside)]

theorem gate_wire {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    W (rename σ C) (n+k) x = W C (n+k) (fun p => x (σ p)) := by
  simpa [index,show ¬ n+k<n from by omega] using wire σ C x (n+k)

theorem eval {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn x) = C.eval (List.ofFn (fun p => x (σ p))) :=
  wire σ C x C.output

end PlaneResearch.RelabelWires

namespace PlaneResearch.PlaneFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.StarOwners
open PlaneResearch.BicliqueStar PlaneResearch.CleanWireModel PlaneResearch.RelabelWires
abbrev V := Fin 42
abbrev forward (u v : V) := u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
abbrev adjacent (p q : V) := forward p q ∨ forward q p
def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨by intro p q h; exact Or.symm h⟩
  loopless := ⟨by decide +kernel⟩
private instance : DecidableRel graph.Adj := fun p q => inferInstanceAs (Decidable (adjacent p q))
def edges : Finset (V × V) := Finset.univ.filter (fun z => forward z.1 z.2)
private def neighbors (a b : V) : Finset V := Finset.univ.filter (fun v => adjacent a v ∧ adjacent b v)
private theorem common : ∀ a b : V, a ≠ b → (neighbors a b).card≤1 := by decide +kernel
theorem noSquare : NoSquare graph := by
  intro a b c d ab bc cd da
  by_cases eq : a=c
  · exact Or.inl eq
  · right
    apply Finset.card_le_one.mp (common a c eq)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩

private def recorded : Finset (Sym2 V) := edges.image (fun p => s(p.1,p.2))
private theorem recordedCount : recorded.card=105 := by decide +kernel
theorem edge_count_le : 105≤graph.edgeFinset.card := by
  rw [←recordedCount]
  apply Finset.card_le_card
  intro e he
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (show graph.Adj p.1 p.2 from Or.inl (Finset.mem_filter.mp hp).2)

private def left (i : Fin 21) : V := ⟨i.val,by omega⟩
private def right (i : Fin 21) : V := ⟨21+i.val,by omega⟩
private def slot (v : V) : Fin 21 := ⟨v.val%21,Nat.mod_lt _ (by decide)⟩
private theorem matching : ∀ i, graph.Adj (left i) (right i) := by decide +kernel
private theorem inverse : ∀ i, slot (left i)=i ∧ slot (right i)=i := by decide +kernel

theorem cover_lower (K : Finset V) (cover : ∀ u v, graph.Adj u v → u ∈ K ∨ v ∈ K) : 21≤K.card := by
  let pick (i : Fin 21) := if left i ∈ K then left i else right i
  have undo (i : Fin 21) : slot (pick i)=i := by
    dsimp only [pick]
    split
    · exact (inverse i).1
    · exact (inverse i).2
  have bound : (Finset.univ : Finset (Fin 21)).card≤K.card := by
    apply Finset.card_le_card_of_injOn pick
    · intro i _
      by_cases l : left i ∈ K
      · simpa [pick,l] using l
      · simpa [pick,l] using (cover _ _ (matching i)).resolve_left l
    · intro i _ j _ h
      exact (undo i).symm.trans ((congrArg slot h).trans (undo j))
  simpa using bound


def mark (v : V) := decide (v.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))
theorem independent : ∀ p q : V, mark p=true → mark q=true → ¬adjacent p q := by decide +kernel
private def labelMap (t : Fin 21) (d : Bool) (v : V) : V :=
  let a := (if d then t.val+21-v.val%21 else t.val+v.val%21)%21
  ⟨(if (decide (21≤v.val) != d) then 21 else 0)+a, by dsimp [a]; split <;> omega⟩
private def invShift (t : Fin 21) (d : Bool) : Fin 21 :=
  if d then t else ⟨(21-t.val)%21,Nat.mod_lt _ (by decide)⟩
private theorem left_inv : ∀ t d v, labelMap (invShift t d) d (labelMap t d v)=v := by decide +kernel
private theorem right_inv : ∀ t d v, labelMap t d (labelMap (invShift t d) d v)=v := by decide +kernel
def perm (t : Fin 21) (d : Bool) : Equiv.Perm V :=
  ⟨labelMap t d,labelMap (invShift t d) d,left_inv t d,right_inv t d⟩
private theorem equiv_adj : ∀ t d p q, adjacent (labelMap t d p) (labelMap t d q) ↔ adjacent p q := by decide +kernel
private theorem orbit : ∀ p q : V, ¬adjacent p q →
    ∃ t : Fin 21, ∃ d : Bool, mark (labelMap t d p)=true ∧ mark (labelMap t d q)=true := by decide +kernel
abbrev Correct (C : Circuit) := ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
  ∃ u v, forward u v ∧ x u=true ∧ x v=true
abbrev CorrectSym (C : Circuit) := ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
  ∃ u v, adjacent u v ∧ x u=true ∧ x v=true
theorem symmetrize (C : Circuit) : Correct C ↔ CorrectSym C := by
  have eqv (x : V → Bool) : (∃ u v, forward u v ∧ x u=true ∧ x v=true) ↔
      (∃ u v, adjacent u v ∧ x u=true ∧ x v=true) := by
    constructor
    · rintro ⟨u,v,h,a,b⟩
      exact ⟨u,v,Or.inl h,a,b⟩
    · rintro ⟨u,v,h|h,a,b⟩
      · exact ⟨u,v,h,a,b⟩
      · exact ⟨v,u,h,b,a⟩
  exact ⟨fun h x => (h x).trans (eqv x),fun h x => (h x).trans (eqv x).symm⟩
lemma relabel_correct (C : Circuit) (hc : CorrectSym C) (σ : Equiv.Perm V)
    (pres : ∀ a b, adjacent (σ a) (σ b) ↔ adjacent a b) : CorrectSym (rename σ C) := by
  intro x
  rw [PlaneResearch.RelabelWires.eval,hc]
  constructor
  · rintro ⟨p,q,pq,hp,hq⟩
    exact ⟨σ p,σ q,(pres p q).mpr pq,hp,hq⟩
  · rintro ⟨p,q,pq,hp,hq⟩
    refine ⟨σ.symm p,σ.symm q,(pres _ _).mp (by simpa using pq),by simpa using hp,by simpa using hq⟩

theorem normalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x u = true ∧ x v = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 124 ∧
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x u = true ∧ x v = true) ∧
        (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = some g ∧ g.op = .and ∧ (D.wires (List.ofFn (fun v : Fin 42 => decide (v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))))).getD (42 + k) false = true) := by
  intro C hm hs hc
  have correct := (symmetrize C).mp hc
  have unclean : ¬PairClean graph C := by
    intro clean
    have price := ConditionalGraphLower.bound (t:=21) graph C ⟨0,21,by decide⟩
      (fun a b c d _ ac _ _ bd _ ab bc cd da => (noSquare a b c d ab bc cd da).elim ac bd)
      cover_lower hm correct clean
    have ed : graph.edgeSet.ncard=graph.edgeFinset.card := by
      rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
    have := edge_count_le
    omega
  have bad : ∃ (k : ℕ) (hk : k<C.gates.length), C.gates[k].op=.and ∧
      ∃ p q : V, W C (42+k) (pair p q)=true ∧ ¬adjacent p q := by
    by_contra! none
    exact unclean (fun k hk op p q h => none k hk op p q h)
  obtain ⟨k,hk,op,p,q,on',no⟩ := bad
  obtain ⟨t,d,hp,hq⟩ := orbit p q no
  let σ := perm t d
  let D := rename σ C
  have dm : Monotone2 D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [gateMap] using hm a ha
  have dc : Correct D := (symmetrize D).mpr (relabel_correct C correct σ (equiv_adj t d))
  have rel (i : V) (h : pair p q i=true) : mark (σ i)=true := by
    rcases (of_decide_eq_true h : i=p ∨ i=q) with rfl|rfl
    · exact hp
    · exact hq
  have active := wire_mono C (fun g h => by simpa using (hm g h).1) (pair p q) (fun i => mark (σ i)) rel (42+k) on'
  refine ⟨D,dm,(size_eq σ C).le.trans hs,dc,k,gateMap σ C.gates[k],?_,op,?_⟩
  · simp [D,rename,List.getElem?_map,hk]
  · exact (gate_wire σ C k mark).trans active

end PlaneResearch.PlaneFour
