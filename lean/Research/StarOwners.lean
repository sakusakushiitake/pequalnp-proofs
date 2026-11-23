import Research.UnrestrictedOr
import Mathlib.Combinatorics.SimpleGraph.VertexCover

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

private lemma input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) : W C i.val x=x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i.val false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using i.isLt),List.getD_eq_getElem _ _ (by simpa using i.isLt),
    List.getElem_ofFn]

lemma gate {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (x : Fin n → Bool) :
    W C (n+k) x = (C.gates[k]).op.eval ((C.gates[k]).inputs.map (fun j => if j<n+k then W C j x else false)) := by
  simpa only [W,List.length_ofFn,Circuit.wires,wiresFrom] using getD_wiresFrom_gate C.gates (List.ofFn x) k hk

private lemma or_on {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length)
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
