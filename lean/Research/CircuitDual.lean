import Research.UnrestrictedOr

namespace PlaneResearch.CircuitDual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.TripleSystems (wiresFrom length_wiresFrom)

def gate (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.all (fun j => decide (j<n)) then ⟨.or,g.inputs⟩ else ⟨.and,[]⟩
  | .or => ⟨.and,g.inputs.filter (fun j => decide (j<n))⟩
  | .not => match g.inputs with
    | i::_ => if i<n then ⟨.not,[i]⟩ else ⟨.or,[]⟩
    | [] => ⟨.or,[]⟩
  | _ => ⟨.or,[]⟩

def gates : ℕ → List Gate → List Gate
  | _,[] => []
  | n,g::gs => gate n g :: gates (n+1) gs

theorem length_gates (n : ℕ) (gs : List Gate) : (gates n gs).length=gs.length := by
  induction gs generalizing n <;> simp_all [gates]

lemma neg_read (w : List Bool) {i : ℕ} (h : i<w.length) :
    (w.map (!·)).getD i false = !(w.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map,List.getD_eq_getElem _ _ h]

lemma eval_gate (w : List Bool) (g : Gate)
    (allowed : g.op=.and ∨ g.op=.or ∨ g.op=.not) (arity : g.inputs.length≤2) :
    (gate w.length g).op.eval ((gate w.length g).inputs.map (fun i => (w.map (!·)).getD i false)) =
      !(g.op.eval (g.inputs.map (fun i => w.getD i false))) := by
  obtain ⟨op,args⟩ := g
  change op=.and ∨ op=.or ∨ op=.not at allowed
  change args.length≤2 at arity
  cases args with
  | nil => rcases allowed with rfl|rfl|rfl <;> rfl
  | cons i tail =>
    cases tail with
    | nil =>
      by_cases hi : i<w.length
      · rcases allowed with rfl|rfl|rfl <;> simp [gate,GateOp.eval,hi,neg_read w hi]
      · have off := List.getD_eq_default w false (Nat.le_of_not_lt hi)
        rcases allowed with rfl|rfl|rfl <;> simp [gate,GateOp.eval,hi,off]
    | cons j rest =>
      cases rest with
      | cons _ _ => simp at arity
      | nil =>
        by_cases hi : i<w.length <;> by_cases hj : j<w.length
        all_goals first | have ri := neg_read w hi | have ri := List.getD_eq_default w false (Nat.le_of_not_lt hi)
        all_goals first | have rj := neg_read w hj | have rj := List.getD_eq_default w false (Nat.le_of_not_lt hj)
        all_goals rcases allowed with rfl|rfl|rfl <;> simp [gate,GateOp.eval,hi,hj,ri,rj]

theorem wires_dual (gs : List Gate) (w : List Bool) (ok : FanInTwo ⟨gs,0⟩) :
    wiresFrom (gates w.length gs) (w.map (!·))=(wiresFrom gs w).map (!·) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have step := eval_gate w g (ok g List.mem_cons_self).1 (ok g List.mem_cons_self).2
    have tailok : FanInTwo ⟨gs,0⟩ := fun a ha => ok a (List.mem_cons_of_mem _ ha)
    change wiresFrom (gates (w.length+1) gs)
      (w.map (!·) ++ [(gate w.length g).op.eval ((gate w.length g).inputs.map (fun i => (w.map (!·)).getD i false))]) =
      (wiresFrom gs (w++[v])).map (!·)
    rw [step]
    simpa [v] using ih (w++[v]) tailok

def circuit (n : ℕ) (C : Circuit) : Circuit := ⟨gates n C.gates,C.output⟩

theorem dual_eval (C : Circuit) (x : List Bool) (ok : FanInTwo C)
    (valid : C.output<x.length+C.size) :
    (circuit x.length C).eval (x.map (!·)) = !(C.eval x) := by
  change (wiresFrom (gates x.length C.gates) (x.map (!·))).getD C.output false = _
  rw [wires_dual C.gates x ok]
  apply neg_read
  rwa [length_wiresFrom]

end PlaneResearch.CircuitDual
