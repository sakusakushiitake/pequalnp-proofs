import Research.StarOwners
import Research.BicliqueStar

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
