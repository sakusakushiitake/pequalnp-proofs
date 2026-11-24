import Mathlib
import PEqualNP.Defs

namespace NegationReplacement

variable {α ι : Type*} [Fintype α] [DecidableEq α]

def hit (X S : Finset α) : Prop := ∃ p ∈ X, p ∈ S
def increasing (u : Finset α → Prop) : Prop := ∀ ⦃X Y⦄, X ⊆ Y → u X → u Y
def monotoneTail (C : ι → Finset α → Prop → Prop) : Prop :=
  ∀ i ⦃X Y : Finset α⦄ ⦃b c : Prop⦄, X ⊆ Y → (b → c) → C i X b → C i Y c
def correct (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (u : Finset α → Prop) : Prop :=
  ∀ i X, C i X (u X) ↔ hit X (S i)
def needed (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (p : α) : Prop :=
  ∃ i, p ∈ S i ∧ ¬ C i {p} False
def blocked (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (i : ι) : Prop :=
  C i (S i)ᶜ True

private theorem off (A : Finset α) : ¬hit Aᶜ A := by
  rintro ⟨p,hp,ha⟩
  exact (Finset.mem_compl.mp hp) ha

theorem boundary (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (h u : Finset α → Prop)
    (mon : monotoneTail C) (old : correct C S h) (inc : increasing u) :
    correct C S u ↔ (∀ p, needed C S p → u {p}) ∧ (∀ i, blocked C S i → ¬ u (S i)ᶜ) := by
  classical
  constructor
  · intro good
    constructor
    · rintro p ⟨i,pi,required⟩
      by_contra absent
      have v := (good i {p}).mpr ⟨p,by simp,pi⟩
      exact required (mon i (Finset.Subset.refl _) (fun hp => absent hp) v)
    · intro i bad hu
      exact off _ ((good i _).mp (mon i (Finset.Subset.refl _) (fun _ => hu) bad))
  · rintro ⟨positive,negative⟩ i X
    constructor
    · intro yes
      by_contra no
      have sub : X ⊆ (S i)ᶜ := fun p hp => Finset.mem_compl.mpr (fun ps => no ⟨p,hp,ps⟩)
      have bad : blocked C S i := mon i sub (fun _ => trivial) yes
      have ux : ¬ u X := fun hX => negative i bad (inc sub hX)
      exact off _ ((old i _).mp (mon i sub (fun b => (ux b).elim) yes))
    · rintro ⟨p,px,ps⟩
      have sub := Finset.singleton_subset_iff.mpr px
      by_cases easy : C i {p} False
      · exact mon i sub False.elim easy
      · have ux := inc sub (positive p ⟨i,ps,easy⟩)
        exact mon i sub (fun _ => ux) ((old i {p}).mpr ⟨p,by simp,ps⟩)

theorem exists_iff (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (h : Finset α → Prop)
    (mon : monotoneTail C) (old : correct C S h) :
    (∃ u : Finset α → Prop, increasing u ∧ correct C S u) ↔
      ∀ p i, needed C S p → blocked C S i → p ∈ S i := by
  classical
  constructor
  · rintro ⟨u,inc,good⟩ p i hp hi
    by_contra absent
    have test := (boundary C S h u mon old inc).mp good
    exact test.2 i hi (inc (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr absent)) (test.1 p hp))
  · intro compatible
    let u := fun X : Finset α => ∃ p ∈ X, needed C S p
    have inc : increasing u := by
      rintro X Y sub ⟨p,px,need⟩
      exact ⟨p,sub px,need⟩
    refine ⟨u,inc,(boundary C S h u mon old inc).mpr ⟨fun p hp => ⟨p,by simp,hp⟩,?_⟩⟩
    rintro i hi ⟨p,pc,hp⟩
    exact (Finset.mem_compl.mp pc) (compatible p i hp hi)

theorem linear_dichotomy (C : ι → Finset α → Prop → Prop) (S : ι → Finset α) (h : Finset α → Prop)
    (mon : monotoneTail C) (old : correct C S h)
    (i j : ι) (bi : blocked C S i) (bj : blocked C S j) (linear : (S i ∩ S j).card ≤ 1) :
    correct C S (fun _ => False) ∨ (∃ p : α, correct C S (fun X => p ∈ X)) ∨
      ∃ p k, needed C S p ∧ blocked C S k ∧ p ∉ S k ∧ h {p} ∧ ¬h (S k)ᶜ := by
  classical
  by_cases conflict : ∃ p k, needed C S p ∧ blocked C S k ∧ p ∉ S k
  · obtain ⟨p,k,np,bk,pk⟩ := conflict
    obtain ⟨l,pl,nl⟩ := np
    refine Or.inr (Or.inr ⟨p,k,⟨l,pl,nl⟩,bk,pk,?_,?_⟩)
    · by_contra x
      exact nl (mon l (Finset.Subset.refl _) (fun z => x z) ((old l {p}).mpr ⟨p,by simp,pl⟩))
    · intro hC
      exact off _ ((old k _).mp (mon k (Finset.Subset.refl _) (fun _ => hC) bk))
  have ok (p : α) (k : ι) (hp : needed C S p) (hk : blocked C S k) : p ∈ S k := by
    by_contra np
    exact conflict ⟨p,k,hp,hk,np⟩
  by_cases any : ∃ p, needed C S p
  · obtain ⟨p,hp⟩ := any
    have inc : increasing (fun X => p ∈ X) := fun _ _ sub => @sub p
    refine Or.inr (Or.inl ⟨p,(boundary C S h _ mon old inc).mpr ⟨?_,?_⟩⟩)
    · intro q hq
      have hmem (a : α) (ha : needed C S a) : a ∈ S i ∩ S j :=
        Finset.mem_inter.mpr ⟨ok a i ha bi,ok a j ha bj⟩
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp linear) _ (hmem p hp) _ (hmem q hq))
    · intro k hk px
      exact (Finset.mem_compl.mp px) (ok p k hp hk)
  · left
    apply (boundary C S h _ mon old (fun _ _ _ => id)).mpr
    exact ⟨fun p hp => any ⟨p,hp⟩,fun _ _ => id⟩

end NegationReplacement

namespace NegationReplacement.GateList
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

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


def inputs {n : ℕ} (X : Finset (Fin n)) := List.ofFn (fun p => decide (p ∈ X))

theorem length_wires (gs : List Gate) (w : List Bool) : (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]
    simp; omega

theorem inputs_mono {n : ℕ} {X Y : Finset (Fin n)} (sub : X ⊆ Y) (i : ℕ) :
    (inputs X).getD i false = true → (inputs Y).getD i false = true := by
  intro hi
  by_cases h : i<n
  · unfold inputs at hi ⊢
    rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn] at hi ⊢
    exact decide_eq_true (sub (of_decide_eq_true hi))
  · rw [List.getD_eq_default _ _ (by simp [inputs]; omega)] at hi
    contradiction

noncomputable def tail {n : ℕ} {ι : Type*} (pre post : List Gate) (out : ι → ℕ)
    (i : ι) (X : Finset (Fin n)) (b : Prop) : Prop := by
  classical
  exact (wiresFrom post (wiresFrom pre (inputs X) ++ [decide b])).getD (out i) false = true

def signal {n : ℕ} (pre : List Gate) (g : Gate) (X : Finset (Fin n)) : Prop :=
  g.op.eval (g.inputs.map fun j => (wiresFrom pre (inputs X)).getD j false) = true

theorem tail_agrees {n : ℕ} {ι : Type*} (pre post : List Gate) (g : Gate) (out : ι → ℕ)
    (i : ι) (X : Finset (Fin n)) :
    tail pre post out i X (signal pre g X) ↔
      Circuit.eval ⟨pre ++ g :: post,out i⟩ (inputs X) = true := by
  simp [tail,signal,Circuit.eval,Circuit.wires,wiresFrom,List.foldl_append]

theorem tail_mono {n : ℕ} {ι : Type*} (pre post : List Gate) (out : ι → ℕ)
    (hp : ∀ g ∈ pre, g.op=GateOp.and ∨ g.op=GateOp.or)
    (hq : ∀ g ∈ post, g.op=GateOp.and ∨ g.op=GateOp.or) :
    monotoneTail (tail (n:=n) pre post out) := by
  classical
  intro i X Y b c sub bc
  unfold tail
  let A := wiresFrom pre (inputs X)
  let B := wiresFrom pre (inputs Y)
  have len : A.length=B.length := by simp [A,B,length_wires,inputs]
  apply wiresFrom_mono post hq _ _ (by simp [len] : (A++[decide b]).length=(B++[decide c]).length)
  intro j hj
  by_cases small : j<A.length
  · rw [List.getD_append _ _ _ _ small] at hj
    rw [List.getD_append _ _ _ _ (by omega : j<B.length)]
    exact wiresFrom_mono pre hp _ _ (by simp [inputs]) (inputs_mono sub) j hj
  by_cases eq : j=A.length
  · subst j
    rw [getD_snoc_eq] at hj
    rw [len,getD_snoc_eq]
    exact decide_eq_true (bc (of_decide_eq_true hj))
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

theorem circuit_criterion {n : ℕ} {ι : Type*} (pre post : List Gate) (g : Gate) (out : ι → ℕ)
    (S : ι → Finset (Fin n))
    (hp : ∀ G ∈ pre, G.op=GateOp.and ∨ G.op=GateOp.or)
    (hq : ∀ G ∈ post, G.op=GateOp.and ∨ G.op=GateOp.or)
    (computes : ∀ i X, Circuit.eval ⟨pre ++ g :: post,out i⟩ (inputs X) = true ↔ hit X (S i)) :
    (∃ u : Finset (Fin n) → Prop, increasing u ∧ correct (tail pre post out) S u) ↔
      ∀ p i, needed (tail pre post out) S p → blocked (tail pre post out) S i → p ∈ S i :=
  exists_iff _ _ (signal pre g) (tail_mono _ _ _ hp hq)
    (fun i X => (tail_agrees pre post g out i X).trans (computes i X))

end NegationReplacement.GateList
