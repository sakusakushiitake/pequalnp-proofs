import Mathlib
import PEqualNP.Defs

-- OR-closure table and wire-prefix identities adapted from L-meta-1505.
namespace PlaneResearch.JunkTrace
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

private lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

private def runTable (row : List (List ℕ) → Gate → List ℕ) (gs : List Gate) :=
  gs.foldl (fun t g => t ++ [row t g]) []

private lemma tableNext (row : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (g : Gate) :
    runTable row (gs++[g]) = runTable row gs ++ [row (runTable row gs) g] := by
  simp [runTable,List.foldl_append]

private lemma tableLength (row : List (List ℕ) → Gate → List ℕ) (gs : List Gate) :
    (runTable row gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [tableNext,ih]

private lemma tablePrefix (row : List (List ℕ) → Gate → List ℕ) (pre post : List Gate) :
    runTable row pre <+: runTable row (pre++post) := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [← List.append_assoc,tableNext]
    exact ih.trans (List.prefix_append ..)

private lemma tableGet (row : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (k : ℕ)
    (hk : k < gs.length) :
    (runTable row gs).getD k [] = row (runTable row (gs.take k)) gs[k] := by
  have next : gs.take (k+1)=gs.take k++[gs[k]] := by
    rw [List.take_add_one,List.getElem?_eq_getElem hk]; simp
  obtain ⟨tail,htail⟩ := tablePrefix row (gs.take (k+1)) (gs.drop (k+1))
  rw [List.take_append_drop] at htail
  rw [← htail,List.getD_append _ _ _ _ (by simp [tableLength]; omega),next,tableNext]
  have len : (runTable row (gs.take k)).length = k := by simp [tableLength,Nat.min_eq_left (by omega : k≤gs.length)]
  conv_lhs => arg 2; rw [←len]
  simp [List.getD]

private lemma prefixValue (row : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (k i : ℕ)
    (hk : k≤gs.length) (hi : i<k) :
    (runTable row (gs.take k)).getD i [] = (runTable row gs).getD i [] := by
  obtain ⟨tail,htail⟩ := tablePrefix row (gs.take k) (gs.drop k)
  rw [List.take_append_drop] at htail
  rw [← htail,List.getD_append _ _ _ _ (by simp [tableLength,Nat.min_eq_left hk,hi])]

private def orRow (n : ℕ) (cs : List (List ℕ)) (g : Gate) :=
  letI := gateOpDecEq
  cs.length :: (if g.op = GateOp.or then ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => cs.getD (w - n) [])) else [])

private def coneRow (n : ℕ) (cs : List (List ℕ)) (g : Gate) :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w-n)::cs.getD (w-n) [])

private lemma orEq (n : ℕ) (C : Circuit) : orSets n C = runTable (orRow n) C.gates := rfl
private lemma coneEq (n : ℕ) (C : Circuit) : cones n C = runTable (coneRow n) C.gates := rfl

private lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k<C.gates.length) : gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk]

private lemma orSplit {n k g : ℕ} {C : Circuit} (hk : k<C.gates.length) (rb : ReadsBack n C) :
    OrReaches n C (n+k) g ↔ g=k ∨ (gateAt C k).op=GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, OrReaches n C w g := by
  classical
  have len : (runTable (orRow n) (C.gates.take k)).length=k := by
    simp [tableLength,Nat.min_eq_left (by omega : k≤C.gates.length)]
  unfold OrReaches
  rw [orEq, Nat.add_sub_cancel_left,tableGet _ _ _ hk]
  simp only [Nat.le_add_right, true_and,orRow,len,List.mem_cons, ←gateAt_eq C k hk]
  by_cases op : (gateAt C k).op = GateOp.or
  · simp only [op,ite_true,true_and,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
    apply or_congr_right
    constructor
    · rintro ⟨w,⟨mem,lo,hi⟩,h⟩
      exact ⟨w,mem,lo,(prefixValue (orRow n) C.gates k (w-n) hk.le (by omega)) ▸ h⟩
    · rintro ⟨w,mem,lo,h⟩
      have hi := rb k hk w mem
      exact ⟨w,⟨mem,lo,hi⟩,(prefixValue (orRow n) C.gates k (w-n) hk.le (by omega)).symm ▸ h⟩
  · simp [op]

private lemma inSide {n : ℕ} {C : Circuit} {w : ℕ} {p : Fin n} :
    p ∈ orIn n C w ↔ p.val=w ∨ ∃ k<C.gates.length, OrReaches n C w k ∧
      (gateAt C k).op=GateOp.or ∧ p.val ∈ (gateAt C k).inputs := by simp [orIn]

private lemma andEmpty {n k : ℕ} {C : Circuit} (hk : k<C.gates.length) (rb : ReadsBack n C)
    (op : (gateAt C k).op=GateOp.and) : orIn n C (n+k)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases inSide.mp hp with eq | ⟨z,_,h,zo,_⟩
  · omega
  · rcases (orSplit hk rb).mp h with rfl | ⟨ko,_⟩
    · simp_all
    · simp_all

private lemma throughOr {n k : ℕ} {C : Circuit} (hk : k<C.gates.length) (rb : ReadsBack n C)
    (op : (gateAt C k).op=GateOp.or) (p : Fin n) :
    p ∈ orIn n C (n+k) ↔ ∃ w ∈ (gateAt C k).inputs, p ∈ orIn n C w := by
  constructor
  · intro hp
    rcases inSide.mp hp with eq | ⟨z,hz,h,zo,mem⟩
    · omega
    · rcases (orSplit hk rb).mp h with rfl | ⟨_,w,hw,reach⟩
      · exact ⟨p.val,mem,inSide.mpr (Or.inl rfl)⟩
      · exact ⟨w,hw,inSide.mpr (Or.inr ⟨z,hz,reach,zo,mem⟩)⟩
  · rintro ⟨w,hw,hp⟩
    rcases inSide.mp hp with eq | ⟨z,hz,h,zo,mem⟩
    · exact inSide.mpr (Or.inr ⟨k,hk,(orSplit hk rb).mpr (Or.inl rfl),op,eq ▸ hw⟩)
    · exact inSide.mpr (Or.inr ⟨z,hz,(orSplit hk rb).mpr (Or.inr ⟨op,w,hw,h⟩),zo,mem⟩)

private lemma operands {n k : ℕ} {C : Circuit} (ao : IsAO2 n C) (hk : k<C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0,opnd C k 1] := by
  have len : (gateAt C k).inputs.length=2 := ao.2.2 _ (gateAt_eq C k hk ▸ List.getElem_mem ..)
  unfold opnd
  cases e : (gateAt C k).inputs with
  | nil => simp [e] at len
  | cons u us =>
    cases us with
    | nil => simp [e] at len
    | cons v vs =>
      cases vs with
      | nil => rfl
      | cons t ts => simp [e] at len

private lemma evaluateGate {n k : ℕ} {C : Circuit} (hk : k<C.gates.length) (rb : ReadsBack n C)
    (x : Fin n → Bool) : gateVal n C k x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun u =>
       (C.wires (List.ofFn x)).getD u false) := by
  obtain ⟨pre,post,g,eq,plen,gval⟩ := split_gates C.gates k hk
  let w := pre.foldl stepWire (List.ofFn x)
  have len : w.length=n+k := by simp [w,foldl_stepWire_length,plen]
  have gid : gateAt C k=g := (gateAt_eq C k hk).trans gval
  have args : (g.inputs.map fun u => (C.wires (List.ofFn x)).getD u false) = (g.inputs.map fun u => w.getD u false) := by
    apply List.map_congr_left
    intro u mem
    have low := rb k hk u (gid ▸ mem)
    rw [wires_eq_foldl,eq,List.foldl_append]
    exact foldl_stepWire_getD_lt (g::post) w u (by omega)
  rw [gid,args]
  unfold gateVal
  rw [wires_eq_foldl,eq,List.foldl_append,List.foldl_cons]
  change (post.foldl stepWire (stepWire w g)).getD (n+k) false = _
  rw [foldl_stepWire_getD_lt _ _ _ (by simp [stepWire]; omega)]
  simp [stepWire,List.getD_eq_getElem?_getD,len]

private abbrev val {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) :=
  (C.wires (List.ofFn x)).getD w false
private lemma input {n : ℕ} (C : Circuit) (p : Fin n) (x : Fin n → Bool) : val C p.val x=x p := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD p.val false=x p
  rw [foldl_stepWire_getD_lt _ _ _ (by simpa using p.isLt),List.getD_eq_getElem _ _ (by simpa using p.isLt),List.getElem_ofFn]

private lemma trace {n : ℕ} {C : Circuit} (ao : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (valid : w<n+C.gates.length) (active : val C w x=true) :
    (∃ p ∈ orIn n C w, x p=true ∧ ∀ y, y p=true → val C w y=true) ∨
    ∃ k<C.gates.length, n+k≤w ∧ (gateAt C k).op=.and ∧ gateVal n C k x=true ∧
      ∀ y, gateVal n C k y=true → val C w y=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases lo : w<n
    · let p : Fin n := ⟨w,lo⟩
      exact Or.inl ⟨p,inSide.mpr (Or.inl rfl),(input C p x) ▸ active,fun y hy => (input C p y).trans hy⟩
    let k:=w-n
    have eq : w=n+k := by dsimp [k]; omega
    have hk : k<C.gates.length := by omega
    have on' : gateVal n C k x=true := by change val C (n+k) x=true; rwa [←eq]
    rcases ao.1 _ (gateAt_eq C k hk ▸ List.getElem_mem ..) with op|op
    · exact Or.inr ⟨k,hk,by omega,op,on',fun _ h => eq ▸ h⟩
    rw [evaluateGate hk ao.2.1,op] at on'
    obtain ⟨b,mem,hb⟩ := List.any_eq_true.mp on'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp mem
    have low := ao.2.1 k hk u hu
    have step (y : Fin n → Bool) (hy : val C u y=true) : val C w y=true := by
      rw [eq]
      change gateVal n C k y=true
      rw [evaluateGate hk ao.2.1,op]
      exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨u,hu,hy⟩,rfl⟩
    rcases ih u (by omega) (by omega) hb with ⟨p,pm,px,py⟩|⟨j,jl,jw,jo,jx,jy⟩
    · exact Or.inl ⟨p,eq ▸ (throughOr hk ao.2.1 op p).mpr ⟨u,hu,pm⟩,px,fun y h => step y (py y h)⟩
    · exact Or.inr ⟨j,jl,by omega,jo,jx,fun y h => step y (jy y h)⟩

private lemma singleton_off {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n) :
    graphFun G ∅ (fun i => decide (i=p))=false := by
  simp [graphFun]

private lemma edge_on {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n} (uv : G.Adj u v) :
    graphFun G ∅ (pairInput u v)=true := by
  simp only [graphFun,Finset.notMem_empty,Bool.false_or,exists_false, false_and,decide_false,Bool.or_eq_true,
    decide_eq_true_eq]
  exact ⟨u,v,uv,by simp [pairInput],by simp [pairInput]⟩

private lemma first {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (correct : circuitFun n C=graphFun G ∅) (x : Fin n → Bool) (on' : graphFun G ∅ x=true) :
    ∃ k<C.gates.length, (gateAt C k).op=.and ∧ BelowF G C k ∧ gateVal n C k x=true := by
  have eq (y : Fin n → Bool) : val C C.output y=graphFun G ∅ y := congrFun correct y
  have out := (eq x).trans on'
  have valid : C.output<n+C.gates.length := by
    by_contra! h
    have hh := getD_ge_length (C.wires (List.ofFn x)) C.output (by rw [wires_length]; exact h)
    exact Bool.noConfusion (hh.symm.trans out)
  rcases trace ao x C.output valid out with ⟨p,_,_,hp⟩|⟨k,hl,_,op,act,hy⟩
  · have h := hp (fun i => decide (i=p)) (by simp)
    rw [eq,singleton_off] at h
    contradiction
  · exact ⟨k,hl,op,fun y h => (eq y).symm.trans (hy y h),act⟩

abbrev guarded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) :=
  ∃ g ∈ junk G C, e ∈ gammaE G C g ∧ ∃ p ∈ e, p ∈ wmax G C g
abbrev paired {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) :=
  ∃ g ∈ junk G C, ∃ h ∈ junk G C, g≠h ∧ e ∈ gammaE G C g ∧ e ∈ gammaE G C h ∧
    ∀ x, gateVal n C g x=true → gateVal n C h x=true → graphFun G ∅ x=true

private lemma least_witness (P : ℕ → Prop) (non : ∃ k,P k) : ∃ a,P a ∧ ∀ g,P g → a≤g := by
  classical
  exact ⟨Nat.find non,Nat.find_spec non,fun _ h => Nat.find_min' non h⟩

theorem classify {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (correct : circuitFun n C=graphFun G ∅)
    (e : Sym2 (Fin n)) (miss : e ∈ Ustar G C) : guarded G C e ∨ paired G C e := by
  classical
  letI := gateOpDecEq
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨edge,nostar⟩ := Finset.mem_sdiff.mp miss
    have uv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp edge
    let x := pairInput u v
    let P (k : ℕ) := k<C.gates.length ∧ (gateAt C k).op=.and ∧ BelowF G C k ∧ gateVal n C k x=true
    have non : ∃ k,P k := first ao correct x (edge_on G uv)
    obtain ⟨a,spec,smallest⟩ := least_witness P non
    obtain ⟨ha,op,below,active⟩ := spec
    have top : a ∈ tops G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,op,below⟩
    have io := operands ao ha
    have read (y : Fin n → Bool) : gateVal n C a y=true ↔
        val C (opnd C a 0) y=true ∧ val C (opnd C a 1) y=true := by
      rw [evaluateGate ha ao.2.1,op,io]
      simp [GateOp.eval,val]
    have low (b : Fin 2) : opnd C a b<n+a := by
      apply ao.2.1 a ha
      fin_cases b <;> simp [io]
    have endpoint (p : Fin n) (hp : x p=true) : p ∈ s(u,v) := Sym2.mem_iff.mpr (of_decide_eq_true hp)
    have picked (b : Fin 2) (wOn : val C (opnd C a b) x=true) :
        (∃ p ∈ side C a b, p ∈ s(u,v) ∧ ∀ y, y p=true → val C (opnd C a b) y=true) ∨
        ∃ g ∈ junk G C, s(u,v) ∈ gammaE G C g ∧ ∀ y, gateVal n C g y=true → val C (opnd C a b) y=true := by
      have lt := low b
      rcases trace ao x (opnd C a b) (by omega) wOn with ⟨p,hp,onp,dom⟩|⟨g,hg,wg,gop,gon,dom⟩
      · exact Or.inl ⟨p,hp,endpoint p onp,dom⟩
      · have dirty : ¬BelowF G C g := by
          intro clean
          have h := smallest g ⟨hg,gop,clean,gon⟩
          omega
        unfold BelowF at dirty
        push Not at dirty
        obtain ⟨y,yes,no⟩ := dirty
        have inJ : g ∈ junk G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,gop,hg,y,yes,by simpa using no⟩
        have inE : s(u,v) ∈ gammaE G C g := Finset.mem_filter.mpr ⟨edge,u,v,rfl,gon⟩
        exact Or.inr ⟨g,inJ,inE,dom⟩
    obtain ⟨l,r⟩ := (read x).mp active
    have both (y : Fin n → Bool) (l' : val C (opnd C a 0) y=true) (r' : val C (opnd C a 1) y=true) :=
      below y ((read y).mpr ⟨l',r'⟩)
    rcases picked 0 l with ⟨p,pm,pe,pd⟩|⟨g,gj,ge,gd⟩ <;>
      rcases picked 1 r with ⟨q,qm,qe,qd⟩|⟨h,hj,he,hd⟩
    · have diff : p≠q := by
        rintro rfl
        have yy := both (fun i => decide (i=p)) (pd _ (by simp)) (qd _ (by simp))
        rw [singleton_off] at yy
        contradiction
      have same : s(p,q)=s(u,v) := by
        rcases Sym2.mem_iff.mp pe with rfl|rfl <;> rcases Sym2.mem_iff.mp qe with rfl|rfl <;>
          first | contradiction | rfl | exact Sym2.eq_swap
      exact False.elim (nostar (Finset.mem_biUnion.mpr ⟨a,top,
        Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨pm,qm⟩,same⟩⟩))
    · exact Or.inl ⟨h,hj,he,p,pe,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun y hy py => both y (pd y py) (hd y hy)⟩⟩
    · exact Or.inl ⟨g,gj,ge,q,qe,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun y gy qy => both y (gd y gy) (qd y qy)⟩⟩
    · have compat (y : Fin n → Bool) (gy : gateVal n C g y=true) (hy : gateVal n C h y=true) :=
        both y (gd y gy) (hd y hy)
      have diff : g≠h := by
        rintro rfl
        obtain ⟨_,_,y,yes,no⟩ := (show IsDirtyAnd n G C g from (Finset.mem_filter.mp gj).2)
        exact Bool.noConfusion ((compat y yes yes).symm.trans no)
      exact Or.inr ⟨g,gj,h,hj,diff,ge,he,compat⟩


theorem firstChild : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∀ e ∈ PEqualNP.TopForm.Ustar G C,
      (∃ g ∈ PEqualNP.TopForm.junk G C, e ∈ PEqualNP.TopForm.gammaE G C g ∧ ∃ p ∈ e, p ∈ PEqualNP.TopForm.wmax G C g) ∨ (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C, g ≠ h ∧ e ∈ PEqualNP.TopForm.gammaE G C g ∧ e ∈ PEqualNP.TopForm.gammaE G C h ∧ ∀ x, PEqualNP.EdgeOwnership.gateVal n C g x = true → PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) := @classify

end PlaneResearch.JunkTrace
