import Research.CleanStarOwners

namespace PlaneResearch.PlaneClean
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

def edges : Finset (Fin 26 × Fin 26) := {(0,13),(0,14),(0,16),(0,22),(1,13),(1,15),(1,21),(1,25),(2,14),(2,20),(2,24),(2,25),(3,13),(3,19),(3,23),(3,24),(4,18),(4,22),(4,23),(4,25),(5,17),(5,21),(5,22),(5,24),(6,16),(6,20),(6,21),(6,23),(7,15),(7,19),(7,20),(7,22),(8,14),(8,18),(8,19),(8,21),(9,13),(9,17),(9,18),(9,20),(10,16),(10,17),(10,19),(10,25),(11,15),(11,16),(11,18),(11,24),(12,14),(12,15),(12,17),(12,23)}
def adjacent (p q : Fin 26) : Prop := (p,q) ∈ edges ∨ (q,p) ∈ edges
instance (p q : Fin 26) : Decidable (adjacent p q) := inferInstanceAs (Decidable (_ ∨ _))
def graph : SimpleGraph (Fin 26) where
  Adj := adjacent
  symm := ⟨by intro p q h; exact Or.symm h⟩
  loopless := ⟨by decide +kernel⟩
def tests : Finset (Fin 26 × Fin 26) := Finset.univ.filter (fun z => z.1 ≤ z.2 ∧ ¬adjacent z.1 z.2)
theorem test_count : tests.card = 299 := by decide +kernel

/-- For exactly the 52-edge incidence graph of L-meta-650 these 299 tests
characterize AND gates collectively bounded above by its edge function. -/
theorem test_iff (C : Circuit) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (two : ∀ g ∈ C.gates, g.inputs.length≤2) :
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ z ∈ tests, W C (26+k) (pair z.1 z.2)=false) ↔
    (∀ k g, C.gates[k]?=some g → g.op=.and → ∀ x : Fin 26 → Bool, W C (26+k) x=true →
      ∃ p q, graph.Adj p q ∧ x p=true ∧ x q=true) := by
  rw [←pair_tests_iff (by decide : 0<26) graph C ops two]
  constructor
  · intro clear k g hg op p q on'
    by_contra bad
    rcases le_total p q with pq|qp
    · have inT : (p,q) ∈ tests := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pq,bad⟩
      have no := clear k g hg op (p,q) inT
      change W C (26+k) (pair p q)=false at no
      simp [no] at on'
    · have rev : ¬adjacent q p := fun a => bad (Or.symm a)
      have inT : (q,p) ∈ tests := Finset.mem_filter.mpr ⟨Finset.mem_univ _,qp,rev⟩
      have no := clear k g hg op (q,p) inT
      have sym : pair p q=pair q p := funext (fun i => by simp [pair,or_comm])
      change W C (26+k) (pair q p)=false at no
      simp [sym,no] at on'
  · intro clean k g hg op z hz
    apply Bool.eq_false_iff.mpr
    exact fun h => (Finset.mem_filter.mp hz).2.2 (clean k g hg op z.1 z.2 h)

end PlaneResearch.PlaneClean
