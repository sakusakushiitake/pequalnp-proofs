import Research.UnrestrictedOr

namespace PlaneResearch.SideTables

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.TripleSystems (wiresFrom)

abbrev Table (d : ℕ) := BitVec d

def top (d : ℕ) : Table d := ~~~(0 : BitVec d)

def gateVal {d : ℕ} (g : Gate) (w : List (Table d)) : Table d :=
  let a := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => a.foldr (· &&& ·) (top d)
  | .or => a.foldr (· ||| ·) 0
  | .not => ~~~(a.headD 0)
  | _ => 0

def run {d : ℕ} : List Gate → List (Table d) → List (Table d)
  | [], w => w
  | g::gs, w => run gs (w ++ [gateVal g w])

lemma ext_run {d : ℕ} (gs : List Gate) (w : List (Table d)) :
    ∃ tail, run gs w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    obtain ⟨t,h,len⟩ := ih (w ++ [gateVal g w])
    exact ⟨gateVal g w :: t,by simpa [run] using h,by simp [len]⟩

private lemma get_map {d : ℕ} (w : List (Table d)) (j : Fin d) (i : ℕ) :
    (w.map (fun b => b.getLsbD j.val)).getD i false = (w.getD i 0).getLsbD j.val := by
  by_cases hi : i<w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,List.getD_eq_getElem _ _ hi]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp

private lemma gate_bit {d : ℕ} (g : Gate) (w : List (Table d)) (j : Fin d)
    (allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (gateVal g w).getLsbD j.val = g.op.eval (g.inputs.map fun i =>
      (w.map (fun b => b.getLsbD j.val)).getD i false) := by
  simp only [get_map]
  rcases allowed with op|op|op
  · simp only [gateVal,op,GateOp.eval]
    induction g.inputs with
    | nil => simp [top,j.isLt]
    | cons a xs ih => simp_all
  · simp only [gateVal,op,GateOp.eval]
    induction g.inputs with
    | nil => simp
    | cons a xs ih => simp_all
  · cases ins : g.inputs <;> simp [gateVal,op,ins,GateOp.eval,j.isLt]

theorem sample_bits {d : ℕ} (gs : List Gate) (w : List (Table d)) (j : Fin d)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (run gs w).map (fun b => b.getLsbD j.val) = wiresFrom gs (w.map (fun b => b.getLsbD j.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run,ih _ (fun a ha => allowed a (List.mem_cons_of_mem _ ha))]
    simp only [List.map_append,List.map_cons,List.map_nil,gate_bit g w j (allowed g List.mem_cons_self)]
    rfl

theorem wire_bits {d : ℕ} (gs : List Gate) (w : List (Table d)) (j : Fin d) (o : ℕ)
    (allowed : FanInTwo ⟨gs,0⟩) :
    ((run gs w).getD o 0).getLsbD j.val =
      (Circuit.mk gs o).eval (w.map (fun b => b.getLsbD j.val)) := by
  rw [← get_map,sample_bits gs w j (fun g hg => (allowed g hg).1)]
  rfl

def recipe {d : ℕ} (f a b : Table d) : Prop := f = a &&& b ∨ f = a ||| b ∨ f = ~~~a

instance {d : ℕ} (f a b : Table d) : Decidable (recipe f a b) :=
  inferInstanceAs (Decidable (f = a &&& b ∨ f = a ||| b ∨ f = ~~~a))

private lemma born {d : ℕ} (g : Gate) (w : List (Table d)) (f : Table d)
    (eq : gateVal g w = f) (ok : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (fz : f ≠ 0) (ft : f ≠ top d) (fresh : f ∉ w) :
    ∃ a b, (a ∈ w ∨ a = 0) ∧ (b ∈ w ∨ b = 0) ∧ a ≠ f ∧ b ≠ f ∧ recipe f a b := by
  classical
  have source (i : ℕ) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
    by_cases h : i<w.length
    · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem ..
    · exact Or.inr (List.getD_eq_default _ _ (Nat.le_of_not_lt h))
  have diff (i : ℕ) : w.getD i 0 ≠ f := by
    intro e
    rcases source i with h|h
    · exact fresh (e ▸ h)
    · exact fz (e.symm.trans h)
  obtain ⟨op,len⟩ := ok
  rcases op with op|op|op
  · rcases ins : g.inputs with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
    · exact (ft (by simpa [gateVal,op,ins] using eq.symm)).elim
    · exact (diff a (by simpa [gateVal,op,ins,top] using eq)).elim
    · exact ⟨_,_,source a,source b,diff a,diff b,Or.inl (by simpa [gateVal,op,ins,top] using eq.symm)⟩
    · simp [ins] at len
  · rcases ins : g.inputs with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
    · exact (fz (by simpa [gateVal,op,ins] using eq.symm)).elim
    · exact (diff a (by simpa [gateVal,op,ins] using eq)).elim
    · exact ⟨_,_,source a,source b,diff a,diff b,Or.inr (Or.inl (by simpa [gateVal,op,ins] using eq.symm))⟩
    · simp [ins] at len
  · cases ins : g.inputs with
    | nil => exact (ft (by simpa [gateVal,op,ins,top] using eq.symm)).elim
    | cons a rest =>
      exact ⟨_,0,source a,Or.inr rfl,diff a,Ne.symm fz,Or.inr (Or.inr (by simpa [gateVal,op,ins] using eq.symm))⟩

lemma first_recipe {d : ℕ} (gs : List Gate) (w : List (Table d)) (f : Table d)
    (ok : FanInTwo ⟨gs,0⟩) (fz : f ≠ 0) (ft : f ≠ top d)
    (fresh : f ∉ w) (hit : f ∈ run gs w) :
    ∃ a b, (a ∈ run gs w ∨ a = 0) ∧ (b ∈ run gs w ∨ b = 0) ∧ a ≠ f ∧ b ≠ f ∧ recipe f a b := by
  induction gs generalizing w with
  | nil => exact (fresh hit).elim
  | cons g gs ih =>
    by_cases e : gateVal g w=f
    · obtain ⟨a,b,ha,hb,af,bf,rec⟩ := born g w f e (ok g List.mem_cons_self) fz ft fresh
      obtain ⟨t,h,_⟩ := ext_run (g::gs) w
      have keep (p : Table d) : p ∈ w ∨ p=0 → p ∈ run (g::gs) w ∨ p=0 := by
        rintro (hp|hp)
        · exact Or.inl (h ▸ List.mem_append_left _ hp)
        · exact Or.inr hp
      exact ⟨a,b,keep _ ha,keep _ hb,af,bf,rec⟩
    · apply ih _ (fun a ha => ok a (List.mem_cons_of_mem _ ha)) (by simp [fresh,Ne.symm e]) hit

def possible {α : Type} [DecidableEq α] (k : ℕ) (used : Finset α) :
    List (List (Finset α)) → Bool
  | [] => decide (used.card ≤ k)
  | row :: rest => row.any (fun e => decide ((used ∪ e).card ≤ k) && possible k (used ∪ e) rest)

lemma possible_of {α : Type} [DecidableEq α] (k : ℕ) (H : Finset α) (hk : H.card ≤ k)
    (opts : List (List (Finset α))) (works : ∀ row ∈ opts, ∃ e ∈ row, e ⊆ H)
    (used : Finset α) (sub : used ⊆ H) : possible k used opts = true := by
  induction opts generalizing used with
  | nil => exact decide_eq_true ((Finset.card_le_card sub).trans hk)
  | cons row rest ih =>
    obtain ⟨e,he,good⟩ := works row List.mem_cons_self
    have both := Finset.union_subset sub good
    apply List.any_eq_true.mpr
    exact ⟨e,he,by simp [show (used ∪ e).card ≤ k from (Finset.card_le_card both).trans hk,
      ih (fun r hr => works r (List.mem_cons_of_mem _ hr)) _ both]⟩

/-- The fixed table rows in plan must each select one set of intermediate wire
signatures. Rejecting all covers by k extra signatures proves a circuit lower bound. -/
theorem recipe_lower {d : ℕ} (R T : Finset (Table d)) (k : ℕ)
    (plan : List (Table d × List (Finset (Table d))))
    (rz : 0 ∈ R) (rt : top d ∈ R) (dis : Disjoint R T)
    (needs : ∀ v ∈ plan, v.1 ∈ T)
    (exhaust : ∀ v ∈ plan, ∀ a b : Table d, a ≠ v.1 → b ≠ v.1 → recipe v.1 a b →
      ∃ e ∈ v.2, e ⊆ ({a,b} \ (R ∪ T)))
    (reject : possible k ∅ (plan.map Prod.snd) = false)
    (gs : List Gate) (w : List (Table d)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (outputs : T ⊆ (run gs w).toFinset) :
    T.card+k+1 ≤ gs.length := by
  classical
  obtain ⟨tail,eq,len⟩ := ext_run gs w
  let H := tail.toFinset \ (R ∪ T)
  have Ttail : T ⊆ tail.toFinset := by
    intro x hx
    have h := outputs hx
    rw [eq,List.mem_toFinset,List.mem_append] at h
    exact List.mem_toFinset.mpr (h.resolve_left (fun hw => Finset.disjoint_left.mp dis (raw x hw) hx))
  have dht : Disjoint H T := Finset.disjoint_left.mpr (fun a ha ht =>
    (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ ht))
  have size : H.card+T.card ≤ gs.length := by
    rw [←Finset.card_union_of_disjoint dht,←len]
    exact (Finset.card_le_card (Finset.union_subset Finset.sdiff_subset Ttail)).trans (List.toFinset_card_le tail)
  by_contra! small
  have hk : H.card ≤ k := by omega
  have works (row) (hr : row ∈ plan.map Prod.snd) : ∃ e ∈ row, e ⊆ H := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    have vf := needs v hv
    have vraw : v.1 ∉ R := fun h => Finset.disjoint_left.mp dis h vf
    have fz : v.1 ≠ 0 := fun h => vraw (h ▸ rz)
    have ft : v.1 ≠ top d := fun h => vraw (h ▸ rt)
    obtain ⟨a,b,ha,hb,af,bf,rec⟩ := first_recipe gs w v.1 ok fz ft
      (fun h => vraw (raw _ h)) (List.mem_toFinset.mp (outputs vf))
    obtain ⟨e,he,sub⟩ := exhaust v hv a b af bf rec
    refine ⟨e,he,fun p hp => ?_⟩
    obtain ⟨pair,notBase⟩ := Finset.mem_sdiff.mp (sub hp)
    have mem : p ∈ run gs w ∨ p=0 := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at pair
      rcases pair with rfl|rfl
      · exact ha
      · exact hb
    have hpR : p ∉ R := fun h => notBase (Finset.mem_union_left _ h)
    rcases mem with wire|rfl
    · rw [eq,List.mem_append] at wire
      exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr (wire.resolve_left (fun h => hpR (raw _ h))),notBase⟩
    · exact (hpR rz).elim
  have accepted := possible_of k H hk _ works ∅ (Finset.empty_subset _)
  simp [reject] at accepted

private def tables (d : ℕ) : List (Table d) := (List.range (2^d)).map (BitVec.ofNat d)

private lemma contains_table {d : ℕ} (x : Table d) : x ∈ tables d :=
  List.mem_map.mpr ⟨x.toNat,List.mem_range.mpr x.isLt,by simp⟩

def checkPlan {d : ℕ} (R T : Finset (Table d)) (plan : List (Table d × List (Finset (Table d)))) : Bool :=
  plan.all fun v => (tables d).all fun a => (tables d).all fun b =>
    if a ≠ v.1 ∧ b ≠ v.1 ∧ recipe v.1 a b then
      v.2.any (fun e => decide (e ⊆ ({a,b} \ (R ∪ T)))) else true

theorem recipes_checked {d : ℕ} (R T : Finset (Table d))
    (plan : List (Table d × List (Finset (Table d)))) (ok : checkPlan R T plan = true) :
    ∀ v ∈ plan, ∀ a b : Table d, a ≠ v.1 → b ≠ v.1 → recipe v.1 a b →
      ∃ e ∈ v.2, e ⊆ ({a,b} \ (R ∪ T)) := by
  intro v hv a b af bf rec
  have row := List.all_eq_true.mp ok v hv
  have aa := List.all_eq_true.mp row a (contains_table a)
  have bb := List.all_eq_true.mp aa b (contains_table b)
  rw [if_pos ⟨af,bf,rec⟩] at bb
  obtain ⟨e,he,sub⟩ := List.any_eq_true.mp bb
  exact ⟨e,he,of_decide_eq_true sub⟩

end PlaneResearch.SideTables
