import Research.OneSideLower
import Research.PlaneSearchReduction

namespace PlaneResearch.PlaneSideWitness
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.CleanWireModel
open PlaneResearch.PlaneClean PlaneResearch.PlaneProbeOrbit PlaneResearch.PlaneDirtyTriple
open PlaneResearch.PriorityRectangles
open PlaneResearch.PlaneCleanBound (noSquare cover_lower edge_count_le)
open PlaneResearch.PlaneSearchReduction (output_in_range response)
abbrev V := Fin 26

private instance : DecidableRel graph.Adj := fun p q => inferInstanceAs (Decidable (adjacent p q))
def half (b : Bool) : Finset V := Finset.univ.filter (fun p => decide (p.val < 13)=b)
def CrossPair (p q : V) := decide (p.val < 13) ≠ decide (q.val < 13)
private lemma opposite (b : Bool) : ∀ p q, adjacent p q → Across (half b) p q := by
  unfold Across
  cases b <;> decide +kernel
private lemma other : ∀ p : V, ∃ q : V, CrossPair p q ∧ ¬adjacent p q := by
  unfold CrossPair
  decide +kernel
private lemma partition (b : Bool) : ∀ p q : V, ¬CrossPair p q →
    (p ∈ half b ∧ q ∈ half b) ∨ (p ∉ half b ∧ q ∉ half b) := by
  unfold CrossPair
  cases b <;> decide +kernel

private def extended (b : Bool) : SimpleGraph V where
  Adj p q := adjacent p q ∨ (p ≠ q ∧ p ∉ half b ∧ q ∉ half b)
  symm := ⟨by
    intro p q h
    rcases h with h|⟨ne,hp,hq⟩
    · exact Or.inl (Or.symm h)
    · exact Or.inr ⟨ne.symm,hq,hp⟩⟩
  loopless := ⟨by
    intro p h
    rcases h with h|h
    · exact graph.loopless.irrefl p h
    · exact h.1 rfl⟩

def MixedDirty (C : Circuit) := ∃ p q, CrossPair p q ∧ ¬adjacent p q ∧ Fires C (pair p q)
def SideDirty (C : Circuit) (b : Bool) :=
  ∃ p ∈ half b, ∃ q ∈ half b, p ≠ q ∧ Fires C (pair p q)

/-- If all mixed nonincidence pairs are clear, a small correct circuit must
have some AND accepting a pair of distinct vertices on each side separately. -/
theorem either_both (C : Circuit) (hm : Mono C) (hc : Correct C) (small : C.size≤63) :
    MixedDirty C ∨ (SideDirty C true ∧ SideDirty C false) := by
  classical
  by_cases mixed : MixedDirty C
  · exact Or.inl mixed
  right
  have ops := fun g h => (hm g h).1
  have two := fun g h => (hm g h).2
  have quiet (p : V) : ¬ Fires C (pair p p) := by
    rintro ⟨k,g,lookup,op,f⟩
    obtain ⟨q,diff,miss⟩ := other p
    have up := wire_mono C ops (pair p p) (pair p q) (fun i hi => by
      rcases (of_decide_eq_true hi : i=p ∨ i=p) with h|h <;> exact decide_eq_true (Or.inl h)) (26+k) f
    exact mixed ⟨p,q,diff,miss,k,g,lookup,op,up⟩
  have needed (b : Bool) : SideDirty C b := by
    by_contra no
    have clean : PairClean (extended b) C := by
      intro k hk op p q active
      have fires : Fires C (pair p q) := ⟨k,C.gates[k],List.getElem?_eq_getElem hk,op,active⟩
      by_cases edge : adjacent p q
      · exact Or.inl edge
      have diff : p ≠ q := by
        rintro rfl
        exact quiet p fires
      have same : ¬CrossPair p q := fun cross => mixed ⟨p,q,cross,edge,fires⟩
      rcases partition b p q same with ⟨hp,hq⟩|⟨hp,hq⟩
      · exact (no ⟨p,hp,q,hq,diff,fires⟩).elim
      · exact Or.inr ⟨diff,hp,hq⟩
    let o : Node 26 C := ⟨C.output,output_in_range C hc⟩
    obtain ⟨off,on'⟩ := response C hc
    obtain ⟨K,cover,bound⟩ := one_side_lower graph noSquare (half b) (opposite b)
      (extended b) (fun _ _ h => h.elim Or.inr (fun x => Or.inl x.2)) C o ops two clean off on'
    have coverSize := cover_lower K cover
    have edgeSize := edge_count_le
    change C.gates.length≤63 at small
    omega
  exact ⟨needed true,needed false⟩

end PlaneResearch.PlaneSideWitness
