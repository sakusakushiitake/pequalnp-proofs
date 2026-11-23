import Research.CleanStarOwners

namespace PlaneResearch.CleanProbeFamily
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∈ S)
def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :=
  ∀ p ∈ S, ∀ q ∈ S, ¬G.Adj p q
def Covers {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Finset (Fin n))) :=
  ∀ p q, ¬G.Adj p q → ∃ S ∈ F, p ∈ S ∧ q ∈ S

/-- An independent-set cover of all nonedge pairs, with repeated endpoints
allowed, tests every AND of a fixed circuit on all independent inputs. -/
theorem sufficient {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n))
    (F : Finset (Finset (Fin n))) (ind : ∀ S ∈ F, Independent G S) (covers : Covers G F)
    (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2) :
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ S ∈ F, W C (n+k) (indicator S)=false) ↔
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ x : Fin n → Bool, W C (n+k) x=true →
      ∃ p q, G.Adj p q ∧ x p=true ∧ x q=true) := by
  constructor
  · intro clear
    apply (pair_tests_iff hn G C ops two).mp
    intro k g hg ga p q on'
    by_contra no
    obtain ⟨S,hS,hp,hq⟩ := covers p q no
    have lift := wire_mono C ops (pair p q) (indicator S) (fun i hi => by
      rcases (of_decide_eq_true hi : i=p ∨ i=q) with rfl|rfl
      · exact decide_eq_true hp
      · exact decide_eq_true hq) (n+k) on'
    simp [clear k g hg ga S hS] at lift
  · intro clean k g hg ga S hS
    apply Bool.eq_false_iff.mpr
    intro on'
    obtain ⟨p,q,adj,hp,hq⟩ := clean k g hg ga (indicator S) on'
    exact ind S hS p (of_decide_eq_true hp) q (of_decide_eq_true hq) adj

private def witness {n : ℕ} (p q : Fin n) : Circuit := ⟨[⟨.and,[p.val,q.val]⟩],n⟩
private lemma value {n : ℕ} (p q : Fin n) (x : Fin n → Bool) :
    W (witness p q) n x=(x p && x q) := by
  have eq := gate (witness p q) 0 (by simp [witness]) x
  simpa [witness,GateOp.eval,p.isLt,q.isLt,input] using eq

/-- Necessity holds for tests required to certify all monotone binary
circuits. One binary AND detects an uncovered nonedge pair. -/
theorem necessary {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Finset (Fin n)))
    (valid : ∀ C : Circuit, (∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) →
      (∀ g ∈ C.gates, g.inputs.length≤2) →
      (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ S ∈ F, W C (n+k) (indicator S)=false) →
      ∀ k g, C.gates[k]?=some g → g.op=.and → ∀ a b : Fin n, W C (n+k) (pair a b)=true → G.Adj a b) :
    Covers G F := by
  intro p q nonedge
  by_contra! uncovered
  let C := witness p q
  have ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or := by simp [C,witness]
  have two : ∀ g ∈ C.gates, g.inputs.length≤2 := by simp [C,witness]
  have test (k) (g : Gate) (hg : C.gates[k]?=some g) (_ : g.op=.and) (S) (hS : S ∈ F) :
      W C (n+k) (indicator S)=false := by
    obtain ⟨hk,_⟩ := List.getElem?_eq_some_iff.mp hg
    have kz : k=0 := by simpa [C,witness] using hk
    subst k
    simp only [Nat.add_zero,C,value,Bool.and_eq_false_iff]
    by_cases h : p ∈ S
    · exact Or.inr (decide_eq_false (uncovered S hS h))
    · exact Or.inl (decide_eq_false h)
  exact nonedge (valid C ops two test 0 _ rfl rfl p q (by simp [C,value,pair]))

end PlaneResearch.CleanProbeFamily
