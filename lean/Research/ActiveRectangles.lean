import Research.CleanWireModel

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
