import Mathlib
import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph
import PEqualNP.MetaComplexity.Helpers.ForestBound


-- Wire-prefix lemmas adapted from the project proofs of L-meta-1042 and L-meta-907.
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


end PlaneResearch.TripleSystems

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


end PlaneResearch.StarOwners

namespace CoverStar1031
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit PlaneResearch.StarOwners

def marker (g : Gate) := match g.op with
  | .and => some (g.inputs.headD 0)
  | _ => none

private lemma chainMarks (s f : ℕ) (r : List ℕ) : (orChain s f r).filterMap marker=[] := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r v ih => simp [orChain_snoc,List.filterMap_append,ih,marker]

private lemma blockMarks (n : ℕ) (bs : List (ℕ × List ℕ)) :
    ((blockPass n bs).1).filterMap marker=bs.map Prod.fst := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    simp only [blockPass_eq] at *
    simp [List.foldl_append,passStep,CoverCircuit.blockGates,List.filterMap_append,chainMarks,ih,marker]

private lemma firstAssign (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    (assign edges cover).map Prod.fst=cover := by
  induction cover using List.reverseRecOn with
  | nil => rfl
  | append_singleton cover c ih =>
    simp [assign,List.foldl_append] at *
    exact ih

private theorem markSub (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ) :
    ((coverCircuit n edges cover).gates.filterMap marker).Sublist cover := by
  simp only [coverCircuit,List.filterMap_append,chainMarks,List.append_nil,blockMarks]
  have sub := (List.filter_sublist (l:=assign edges cover)
    (p:=fun b : ℕ × List ℕ => decide (0 < b.2.length))).map Prod.fst
  rw [firstAssign] at sub
  exact sub

private theorem markUnique (xs : List Gate) (nd : (xs.filterMap marker).Nodup)
    {i j : ℕ} {g h : Gate} {v : ℕ} (gi : xs[i]?=some g) (hj : xs[j]?=some h)
    (a : marker g=some v) (b : marker h=some v) : i=j := by
  induction xs generalizing i j with
  | nil => simp at gi
  | cons x xs ih =>
    cases i with
    | zero =>
      obtain rfl : x=g := by simpa using gi
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        have mem := List.mem_filterMap.mpr ⟨h,List.mem_of_getElem? hj,b⟩
        simp [List.filterMap_cons,a] at nd
        exact (nd.1 h (List.mem_of_getElem? hj) b).elim
    | succ i =>
      simp only [List.getElem?_cons_succ] at gi
      cases j with
      | zero =>
        obtain rfl : x=h := by simpa using hj
        have mem := List.mem_filterMap.mpr ⟨g,List.mem_of_getElem? gi,a⟩
        simp [List.filterMap_cons,b] at nd
        exact (nd.1 g (List.mem_of_getElem? gi) a).elim
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        apply congrArg Nat.succ
        apply ih _ gi hj
        cases e : marker x with
        | none => simpa [List.filterMap_cons,e] using nd
        | some val => simp [List.filterMap_cons,e] at nd; exact nd.2

private lemma privateEdge {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (cov : ∀ u v, G.Adj u v → u∈T ∨ v∈T)
    (least : ∀ U : Finset (Fin n), (∀ u v, G.Adj u v → u∈U ∨ v∈U) → T.card≤U.card)
    {c : Fin n} (hc : c∈T) : ∃ v, G.Adj c v ∧ v∉T := by
  classical
  by_contra! missing
  have lower := least (T.erase c) (by
    intro u v uv
    by_cases uc : u=c
    · subst u
      exact Or.inr (Finset.mem_erase.mpr ⟨uv.ne.symm,missing v uv⟩)
    by_cases vc : v=c
    · subst v
      exact Or.inl (Finset.mem_erase.mpr ⟨uc,missing u uv.symm⟩)
    rcases cov u v uv with h|h
    · exact Or.inl (Finset.mem_erase.mpr ⟨uc,h⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨vc,h⟩))
  have eq := Finset.card_erase_add_one hc
  omega

private theorem endpoint {n : ℕ} (C : Circuit) (t : ℕ) (g : Gate) (get : C.gates[t]?=some g)
    (op : g.op=.and) (c : Fin n) (raw : c.val∈g.inputs) (p q : Fin n)
    (on : W C (n+t) (pair p q)=true) : p=c ∨ q=c := by
  obtain ⟨lt,rfl⟩ := List.getElem?_eq_some_iff.mp get
  rw [gate C t lt,op] at on
  have allv := List.all_eq_true.mp on
  have v := allv _ (List.mem_map_of_mem raw)
  have cLt : c.val<n+t := by omega
  change (if c.val<n+t then W C c.val (pair p q) else false)=true at v
  rw [if_pos cLt,input] at v
  exact (of_decide_eq_true v : c=p ∨ c=q).imp Eq.symm Eq.symm

abbrev Covers {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :=
  ∀ u v, G.Adj u v → u∈T ∨ v∈T

abbrev Profile {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∀ t g, C.gates[t]?=some g → g.op=.and → ∃ c : Fin n,
    (∃ u v, G.Adj u v ∧ Owns C t u v) ∧ ∀ u v, G.Adj u v → Owns C t u v → u=c ∨ v=c

theorem coverProfile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (cov : Covers G T) (least : ∀ U, Covers G U → T.card≤U.card) :
    Profile G (coverCircuit n (graph_edges n G) (graph_cover T)) := by
  classical
  let C := coverCircuit n (graph_edges n G) (graph_cover T)
  have ops := gates_ops n (graph_edges n G) (graph_cover T)
  have opC (g) (hg : g∈C.gates) : g.op=.and ∨ g.op=.or := (ops _ hg).1.symm
  have hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x)=decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true) := by
    intro x
    exact congrFun (circuitFun_eq_graph n _ _ G (graph_hG n G) (graph_hE n G) (graph_hT n G T cov)) x
  have sub := markSub n (graph_edges n G) (graph_cover T)
  have nd : (C.gates.filterMap marker).Nodup :=
    sub.nodup (T.nodup_toList.map Fin.val_injective)
  have center (k : ℕ) (g : Gate) (found : C.gates[k]?=some g) (op : g.op=.and) :
      ∃ c∈T, marker g=some c.val ∧ c.val∈g.inputs := by
    have gm := List.mem_of_getElem? found
    have map : marker g=some (g.inputs.headD 0) := by simp [marker,op]
    have marked := sub.subset (List.mem_filterMap.mpr ⟨g,gm,map⟩)
    obtain ⟨c,hc,eq⟩ := List.mem_map.mp marked
    have len := (ops _ gm).2
    refine ⟨c,Finset.mem_toList.mp hc,eq ▸ map,eq ▸ ?_⟩
    cases e : g.inputs with
    | nil => simp [e] at len
    | cons a l => simp [e]
  intro k g found op
  obtain ⟨c,ct,mc,raw⟩ := center k g found op
  obtain ⟨v,cv,vt⟩ := privateEdge G T cov least ct
  obtain ⟨j,h,jh,ha,owns⟩ := edge_has_owner G C opC hc c v cv
  obtain ⟨d,dt,md,draw⟩ := center j h jh ha
  have eq : c=d := (endpoint C j h jh ha d draw c v owns.1).resolve_right (fun vd => vt (vd.symm ▸ dt))
  subst d
  have kj := markUnique C.gates nd found jh mc md
  refine ⟨c,⟨c,v,cv,kj.symm ▸ owns⟩,?_⟩
  intro p q _ po
  exact endpoint C k g found op c raw p q po.1

end CoverStar1031

namespace CoverStar1031
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverCircuit

theorem forestTarget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → G.IsAcyclic → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by

  classical
  intro n G inst _ _ forest
  by_cases nonempty : ∃ u v, G.Adj u v
  · let P (k : ℕ) := ∃ T : Finset (Fin n), Covers G T ∧ T.card=k
    have existsP : ∃ k, P k := ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
    obtain ⟨T,cov,sz⟩ := Nat.find_spec existsP
    have least (U : Finset (Fin n)) (cover : Covers G U) : T.card ≤ U.card := by
      rw [sz]
      exact Nat.find_min' existsP ⟨U,cover,rfl⟩
    let C := coverCircuit n (graph_edges n G) (graph_cover T)
    have ops := gates_ops n (graph_edges n G) (graph_cover T)
    have computes := circuitFun_eq_graph n _ _ G (graph_hG n G) (graph_hE n G) (graph_hT n G T cov)
    have upper := size_le n (graph_edges n G) (graph_cover T) (graph_edges_ne_nil n G nonempty)
    rw [graph_edges_length,graph_cover_length] at upper
    refine ⟨C, fun g hg => ⟨(ops g hg).1.symm,by have h := (ops g hg).2; omega⟩,
      fun x => congrFun computes x,?_,coverProfile G T cov least⟩
    intro D dlegal dfun
    have sizeD : HasCircuitSize n _ D.size := ⟨D,fun g hg => ⟨by
      rcases (dlegal g hg).1 with a|o
      · simp [a]
      · simp [o],(dlegal g hg).2⟩,le_rfl,dfun⟩
    have lower := PEqualNP.MetaComplexity.Helpers.Forest.forest_bound n T.card D.size G
      forest nonempty least sizeD
    change C.size+1 ≤ _ at upper
    omega
  · let C : Circuit := ⟨[],n⟩
    refine ⟨C,by simp [C],?_,by simp [C,Circuit.size],by simp [C]⟩
    intro x
    have none : ¬∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
      rintro ⟨u,v,a,_⟩
      exact nonempty ⟨u,v,a⟩
    simp [C,Circuit.eval,Circuit.wires,none,List.getD]

end CoverStar1031
