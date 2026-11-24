import Mathlib
import PEqualNP.Defs

namespace RimFamily

variable {α : Type*} [DecidableEq α]

def CoreOn (T : Finset α) (one : ℕ → α → Prop) (w : ℕ) := ∃ p ∈ T, one w p
def Good (S : ℕ → Finset α) (T : Finset α) (one : ℕ → α → Prop) (P : Finset α) (w : ℕ) :=
  (S w \ P).card ≤ 1 ∧ (∀ p ∈ S w \ P, one w p) ∧ (CoreOn T one w → S w ⊆ P)

lemma good_enlarge {S : ℕ → Finset α} {T P Q : Finset α} {one : ℕ → α → Prop} {w : ℕ}
    (g : Good S T one P w) (sub : P ⊆ Q) : Good S T one Q w := by
  have h : S w \ Q ⊆ S w \ P := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) sub
  exact ⟨(Finset.card_le_card h).trans g.1,fun p hp => g.2.1 p (h hp),fun hc => (g.2.2 hc).trans sub⟩

lemma good_covered {S : ℕ → Finset α} {T P : Finset α} {one : ℕ → α → Prop} {w : ℕ}
    (h : S w ⊆ P) : Good S T one P w := by
  have e : S w \ P = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr h
  exact ⟨by simp [e],by simp [e],fun _ => h⟩

lemma pay {S : ℕ → Finset α} {T P : Finset α} {one : ℕ → α → Prop} {w : ℕ}
    (g : Good S T one P w) : P ⊆ P ∪ S w ∧ (P ∪ S w).card ≤ P.card+1 := by
  refine ⟨Finset.subset_union_left,?_⟩
  have eq : P ∪ S w = P ∪ (S w \ P) := by ext x; simp
  rw [eq]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left g.1 _)

lemma or_pay {S : ℕ → Finset α} {T P : Finset α} {one : ℕ → α → Prop} {w k l : ℕ}
    (gk : Good S T one P k) (gl : Good S T one P l) (sub : S w ⊆ S k ∪ S l)
    (rise : ∀ p, one k p → one w p) (core : CoreOn T one w → CoreOn T one k) :
    ∃ Q, P ⊆ Q ∧ Q.card ≤ P.card+1 ∧ Good S T one Q w := by
  let Q := P ∪ S l
  have rest : S w \ Q ⊆ S k \ P := by
    intro r hr
    obtain ⟨rw',rq⟩ := Finset.mem_sdiff.mp hr
    have out : r ∉ P ∧ r ∉ S l := by simpa [Q] using rq
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp (sub rw')).resolve_right out.2,out.1⟩
  refine ⟨Q,(pay gl).1,(pay gl).2,(Finset.card_le_card rest).trans gk.1,
    fun p hp => rise p (gk.2.1 p (rest hp)),?_⟩
  intro hc p hp
  exact (Finset.mem_union.mp (sub hp)).elim
    (fun h => Finset.mem_union_left _ (gk.2.2 (core hc) h)) (Finset.mem_union_right _)

lemma or_free {S : ℕ → Finset α} {T P L : Finset α} {one : ℕ → α → Prop} {w a b : ℕ}
    (ga : Good S T one P a) (gb : Good S T one P b) (sub : S w ⊆ S a ∪ S b)
    (rise : ∀ p, one a p ∨ one b p → one w p) (rim : S w ⊆ L \ T) (ts : T ⊆ L)
    (rule : (CoreOn T one a ∧ CoreOn T one b) ∨
      (∀ p ∈ L, ∀ z ∈ L, one w p → one w z → p=z)) : Good S T one P w := by
  rcases rule with ⟨ca,cb⟩|single
  · apply good_covered
    intro p hp
    exact (Finset.mem_union.mp (sub hp)).elim (fun h => ga.2.2 ca h) (fun h => gb.2.2 cb h)
  have points (p) (hp : p ∈ S w \ P) : one w p := by
    obtain ⟨hs,np⟩ := Finset.mem_sdiff.mp hp
    apply rise
    exact (Finset.mem_union.mp (sub hs)).elim
      (fun ha => Or.inl (ga.2.1 p (Finset.mem_sdiff.mpr ⟨ha,np⟩)))
      (fun hb => Or.inr (gb.2.1 p (Finset.mem_sdiff.mpr ⟨hb,np⟩)))
  have inL {p} (hp : p ∈ S w \ P) := (Finset.mem_sdiff.mp (rim (Finset.mem_sdiff.mp hp).1)).1
  refine ⟨Finset.card_le_one.mpr (fun p hp z hz => single p (inL hp) z (inL hz) (points p hp) (points z hz)),points,?_⟩
  rintro ⟨z,zt,zo⟩ p hp
  by_contra np
  obtain ⟨pl,pt⟩ := Finset.mem_sdiff.mp (rim hp)
  have eq := single p pl z (ts zt) (points p (Finset.mem_sdiff.mpr ⟨hp,np⟩)) zo
  exact pt (eq ▸ zt)

lemma count_steps {n m : ℕ} (S : ℕ → Finset α) (T : Finset α) (one : ℕ → α → Prop)
    (dead : ℕ → Prop) (charge : Finset ℕ)
    (base : ∀ w, w<n → dead w → Good S T one ∅ w)
    (step : ∀ i < m, ∀ P, (∀ w, w<n+i → dead w → Good S T one P w) →
      ∃ Q, P ⊆ Q ∧ Q.card≤P.card+(if i∈charge then 1 else 0) ∧ (dead (n+i) → Good S T one Q (n+i))) :
    ∃ P, P.card≤charge.card ∧ ∀ w, w<n+m → dead w → Good S T one P w := by
  classical
  have aux (k : ℕ) (hk : k ≤ m) : ∃ P, P.card≤((Finset.range k).filter fun i => i∈charge).card ∧
      ∀ w, w<n+k → dead w → Good S T one P w := by
    induction k with
    | zero => exact ⟨∅,by simp,by simpa using base⟩
    | succ k ih =>
      obtain ⟨P,pc,ok⟩ := ih (by omega)
      obtain ⟨Q,sub,qc,new⟩ := step k (by omega) P ok
      refine ⟨Q,?_,?_⟩
      · rw [Finset.range_add_one,Finset.filter_insert]
        by_cases mem : k∈charge <;> simp [mem] at * <;> omega
      · intro w hw hd
        by_cases eq : w=n+k
        · exact eq ▸ new (eq ▸ hd)
        · exact good_enlarge (ok _ (by omega) hd) sub
  obtain ⟨P,h,good⟩ := aux m (by rfl)
  exact ⟨P,h.trans (Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)),good⟩

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma shape (ins : List ℕ) (lo : 1 ≤ ins.length) (hi : ins.length ≤ 2) :
    ∃ a b, a∈ins ∧ b∈ins ∧ (∀ z, z∈ins → z=a ∨ z=b) ∧
      (∀ c d, ins=[c,d] → c=a ∧ d=b) := by
  cases ins with
  | nil => simp at lo
  | cons a rest =>
    cases rest with
    | nil => exact ⟨a,a,by simp,by simp,by simp,by simp⟩
    | cons b tail =>
      have emp : tail=[] := by cases tail <;> simp_all
      subst tail
      exact ⟨a,b,by simp,by simp,by simp,by simp_all⟩


/-- The same set of points pays for every core-active output of a monotone circuit.
The ambient subset H has no incidence or uniformity assumptions. -/
theorem simultaneous {N : ℕ} (H T : Finset (Fin N)) (subT : T ⊆ H) (gs : List Gate)
    (ops : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (legal : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + (i : ℕ)) (C : Finset (Fin gs.length)) :
    let B := fun v : Fin N => decide (v∉H)
    let extra := fun r v : Fin N => decide (v∉H ∨ v=r)
    let one := fun (w : ℕ) (r : Fin N) => val gs w (fun v => decide (v=r))=true
    let dead := fun w => val gs w B=false
    let S := fun w => (H \ T).filter (fun r => val gs w (extra r)=true)
    (∀ i : Fin gs.length, (gs.get i).op=.and → dead (N+i.val) →
      (∃ u ∈ (gs.get i).inputs, ¬ dead u) →
      ∀ r ∈ S (N+i.val), ¬ one (N+i.val) r → i ∈ C) →
    (∀ i : Fin gs.length, (gs.get i).op=.or → dead (N+i.val) →
      (¬ ∀ u ∈ (gs.get i).inputs, CoreOn T one u) →
      (∃ p∈H, ∃ z∈H, p≠z ∧ one (N+i.val) p ∧ one (N+i.val) z) → i ∈ C) →
    ∃ P : Finset (Fin N), P.card ≤ C.card ∧
      ∀ w, w < N+gs.length → dead w → Good S T one P w := by
  classical
  intro B extra one dead S hA hX
  let charge := C.image Fin.val
  have R (w) : S w ⊆ H \ T := Finset.filter_subset _ _
  have base : ∀ w, w<N → dead w → Good S T one ∅ w := by
    intro w hw hd
    let v : Fin N := ⟨w,hw⟩
    have vl : v ∈ H := by simpa [dead,B,val_input gs _ w hw,v] using hd
    have sing (p) (hp : p∈S w) : p=v := by
      have h := (Finset.mem_filter.mp hp).2
      have : v∉H ∨ v=p := of_decide_eq_true (by simpa only [S,extra,val_input gs _ w hw,v] using h)
      exact (this.resolve_left (not_not.mpr vl)).symm
    simp only [Good,Finset.sdiff_empty]
    refine ⟨Finset.card_le_one.mpr (fun a ha b hb => (sing a ha).trans (sing b hb).symm),?_,?_⟩
    · intro p hp
      simp [one,val_input gs _ w hw,sing p hp,v]
    · rintro ⟨c,ct,co⟩ p hp
      have vc : v=c := of_decide_eq_true (by simpa only [one,val_input gs _ w hw,v] using co)
      exact False.elim ((Finset.mem_sdiff.mp (R w hp)).2 ((sing p hp).trans vc ▸ ct))
  have step : ∀ k < gs.length, ∀ P, (∀ w, w<N+k → dead w → Good S T one P w) →
      ∃ Q, P⊆Q ∧ Q.card≤P.card+(if k∈charge then 1 else 0) ∧ (dead (N+k) → Good S T one Q (N+k)) := by
    intro k hk P ih
    let i : Fin gs.length := ⟨k,hk⟩
    have op := ops gs[k] (List.getElem_mem hk)
    have valid := legal i
    change 1≤gs[k].inputs.length ∧ ∀ a∈gs[k].inputs,a<N+k at valid
    have memcharge (h : i∈C) : k∈charge := Finset.mem_image.mpr ⟨i,h,rfl⟩
    by_cases hd : dead (N+k)
    swap
    · exact ⟨P,Finset.Subset.refl _,by omega,fun contra => (hd contra).elim⟩
    rcases op.1 with andop|orop
    · by_cases active : (S (N+k)).Nonempty
      swap
      · exact ⟨P,Finset.Subset.refl _,by omega,fun _ => good_covered (by simp [Finset.not_nonempty_iff_eq_empty.mp active])⟩
      obtain ⟨r,hr⟩ := active
      obtain ⟨rr,rval⟩ := Finset.mem_filter.mp hr
      have parent : ∃ j ∈ gs[k].inputs, dead j := by
        by_contra! none
        have yes := (val_and gs B k hk andop).mpr (fun j hj =>
          ⟨valid.2 j hj,by simpa [dead] using none j hj⟩)
        exact Bool.noConfusion (yes.symm.trans hd)
      obtain ⟨j,hj,jd⟩ := parent
      have good := ih j (valid.2 j hj) jd
      have carry : S (N+k) ⊆ S j := by
        intro z hz
        obtain ⟨zr,valz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨zr,((val_and gs (extra z) k hk andop).mp valz j hj).2⟩
      by_cases ch : k∈charge
      swap
      · refine ⟨P,Finset.Subset.refl _,by omega,fun _ => ?_⟩
        have incl : S (N+k) \ P ⊆ S j \ P :=
          Finset.sdiff_subset_sdiff carry (Finset.Subset.refl _)
        refine ⟨(Finset.card_le_card incl).trans good.1,?_,?_⟩
        · intro r hr
          by_contra fail
          have rs := (Finset.mem_sdiff.mp hr).1
          have live : ∃ u∈gs[k].inputs, ¬ dead u := by
            by_contra! allDead
            apply fail
            apply (val_and gs _ k hk andop).mpr
            intro u hu
            have uok := ih u (valid.2 u hu) (allDead u hu)
            obtain ⟨rr,vr⟩ := Finset.mem_filter.mp rs
            have ur := ((val_and gs _ k hk andop).mp vr u hu).2
            exact ⟨valid.2 u hu, uok.2.1 r (Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨rr,ur⟩,(Finset.mem_sdiff.mp hr).2⟩)⟩
          exact ch (memcharge (hA i andop hd live r rs fail))
        · rintro ⟨c,ct,cv⟩ r hr
          exact good.2.2 ⟨c,ct,((val_and gs _ k hk andop).mp cv j hj).2⟩ (carry hr)
      exact ⟨P ∪ S j,(pay good).1,by simpa [ch] using (pay good).2,
        fun _ => good_covered (carry.trans Finset.subset_union_right)⟩
    · obtain ⟨a,b,ai,bi,parents,fixed⟩ := shape gs[k].inputs valid.1 op.2
      have ev (x : Fin N → Bool) : val gs (N+k) x=true ↔ val gs a x=true ∨ val gs b x=true := by
        rw [val_or gs x k hk orop]
        constructor
        · rintro ⟨j,hj,_,valj⟩
          rcases parents j hj with rfl|rfl
          · exact Or.inl valj
          · exact Or.inr valj
        · rintro (va|vb)
          · exact ⟨a,ai,valid.2 a ai,va⟩
          · exact ⟨b,bi,valid.2 b bi,vb⟩
      have no : ¬(val gs a B=true ∨ val gs b B=true) := fun h => Bool.noConfusion (((ev B).mpr h).symm.trans hd)
      have ga := ih a (valid.2 a ai) (by simpa [dead] using (not_or.mp no).1)
      have gb := ih b (valid.2 b bi) (by simpa [dead] using (not_or.mp no).2)
      have subs : S (N+k) ⊆ S a ∪ S b := by
        intro r hr
        obtain ⟨mem,yes⟩ := Finset.mem_filter.mp hr
        exact Finset.mem_union.mpr (((ev _).mp yes).imp
          (fun h => Finset.mem_filter.mpr ⟨mem,h⟩) (fun h => Finset.mem_filter.mpr ⟨mem,h⟩))
      have rise (p) : one a p ∨ one b p → one (N+k) p := (ev _).mpr
      have csplit (hc : CoreOn T one (N+k)) : CoreOn T one a ∨ CoreOn T one b := by
        obtain ⟨p,ht,hp⟩ := hc
        exact (((ev _).mp hp).imp (fun h => ⟨p,ht,h⟩) (fun h => ⟨p,ht,h⟩))
      by_cases ch : k∈charge
      · have paid : ∃ Q, P ⊆ Q ∧ Q.card≤P.card+1 ∧ Good S T one Q (N+k) := by
          by_cases cb : CoreOn T one b
          · apply or_pay gb ga (by simpa [Finset.union_comm] using subs) (fun p h => rise p (Or.inr h)) (fun _ => cb)
          · apply or_pay ga gb subs (fun p h => rise p (Or.inl h)) (fun h => (csplit h).resolve_right cb)
        obtain ⟨Q,pq,cq,good⟩ := paid
        exact ⟨Q,pq,by simpa [ch] using cq,fun _ => good⟩
      · refine ⟨P,Finset.Subset.refl _,by omega,fun _ => or_free ga gb subs rise (R _) subT ?_⟩
        by_cases cc : CoreOn T one a ∧ CoreOn T one b
        · exact Or.inl cc
        right
        intro p pl z zl wp wz
        by_contra pz
        apply ch
        apply memcharge
        apply hX i orop hd
        · intro allcore
          exact cc ⟨allcore a ai,allcore b bi⟩
        · exact ⟨p,pl,z,zl,pz,wp,wz⟩
  obtain ⟨P,pc,all⟩ := count_steps S T one dead charge base step

  exact ⟨P,pc.trans Finset.card_image_le,all⟩

/-- Several outputs may cover different parts of the rim. Each core-inactive
output needs at most one additional point beyond the common paid set. -/
theorem union_bound {S : ℕ → Finset α} {T P : Finset α} {one : ℕ → α → Prop}
    (O : Finset ℕ) (good : ∀ w ∈ O, Good S T one P w) [DecidablePred (CoreOn T one)] :
    (O.biUnion S).card ≤ P.card + (O.filter fun w => ¬ CoreOn T one w).card := by
  classical
  let Q := O.filter (fun w => ¬ CoreOn T one w)
  have cover : O.biUnion S ⊆ P ∪ Q.biUnion (fun w => S w \ P) := by
    intro r hr
    obtain ⟨w,wo,wr⟩ := Finset.mem_biUnion.mp hr
    by_cases rp : r ∈ P
    · exact Finset.mem_union_left _ rp
    · have nc : ¬ CoreOn T one w := fun h => rp ((good w wo).2.2 h wr)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨wo,nc⟩,
        Finset.mem_sdiff.mpr ⟨wr,rp⟩⟩)
  have total : (Q.biUnion fun w => S w \ P).card ≤ Q.card := by
    calc
      _ ≤ ∑ w ∈ Q, (S w \ P).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ Q, 1 := Finset.sum_le_sum (fun w hw => (good w (Finset.mem_filter.mp hw).1).1)
      _ = _ := by simp
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left total _))

end RimFamily
