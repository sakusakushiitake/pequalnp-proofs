import Research.PlaneProbeOrbit
import Research.RelabelWires
import Research.CleanProbeFamily

namespace PlaneResearch.PlaneDirtyTriple
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.CleanProbeFamily
open PlaneResearch.PlaneClean PlaneResearch.PlaneProbeOrbit PlaneResearch.RelabelWires

abbrev Correct (C : Circuit) := ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
  ∃ p q, adjacent p q ∧ x p=true ∧ x q=true
abbrev Mono (C : Circuit) := ∀ g ∈ C.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
def Fires (C : Circuit) (x : V → Bool) :=
  ∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ W C (26+k) x=true

private lemma relabel_correct (C : Circuit) (hc : Correct C) (σ : Equiv.Perm V)
    (pres : ∀ a b, adjacent (σ a) (σ b) ↔ adjacent a b) : Correct (rename σ C) := by
  intro x
  rw [PlaneResearch.RelabelWires.eval,hc]
  constructor
  · rintro ⟨p,q,pq,hp,hq⟩
    exact ⟨σ p,σ q,(pres p q).mpr pq,hp,hq⟩
  · rintro ⟨p,q,pq,hp,hq⟩
    refine ⟨σ.symm p,σ.symm q,(pres _ _).mp (by simpa using pq),by simpa using hp,by simpa using hq⟩

private lemma relabel_mono (C : Circuit) (hm : Mono C) (σ : Equiv.Perm V) : Mono (rename σ C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [gateMap] using hm a ha

/-- Normalize a circuit with a dirty AND to the single fixed independent
triple by a size-preserving graph automorphism. -/
theorem normalize (C : Circuit) (hc : Correct C) (hm : Mono C)
    (S : Finset V) (hs : Independent graph S) (dirty : Fires C (indicator S)) :
    ∃ D : Circuit, Correct D ∧ Mono D ∧ D.size=C.size ∧ Fires D (indicator fixed) := by
  classical
  have ops := fun g h => (hm g h).1
  have two := fun g h => (hm g h).2
  have witness : ∃ p q : V, ¬adjacent p q ∧ Fires C (pair p q) := by
    by_contra! bad
    obtain ⟨k,g,atg,op,on'⟩ := dirty
    have h := pair_tests_suffice (by decide : 0<26) graph C ops two (by
      intro t a ht ho p q active
      by_contra no
      exact bad p q no ⟨t,a,ht,ho,active⟩) k g atg op (indicator S) on'
    obtain ⟨p,q,pq,sp,sq⟩ := h
    exact hs p (of_decide_eq_true sp) q (of_decide_eq_true sq) pq
  obtain ⟨p,q,no,k,g,lookup,op,on'⟩ := witness
  obtain ⟨σ,pres,hp,hq⟩ := to_triple p q no
  let D := rename σ C
  have mono := relabel_mono C hm σ
  have rel : ∀ i, pair p q i=true → indicator fixed (σ i)=true := by
    intro i hi
    rcases (of_decide_eq_true hi : i=p ∨ i=q) with rfl|rfl
    · exact decide_eq_true hp
    · exact decide_eq_true hq
  have active := wire_mono C ops (pair p q) (fun i => indicator fixed (σ i)) rel (26+k) on'
  have read : D.gates[k]?=some (gateMap σ g) := by simp [D,rename,List.getElem?_map,lookup]
  exact ⟨D,relabel_correct C hc σ pres,mono,size_eq σ C,k,gateMap σ g,read,op,
    (gate_wire σ C k (indicator fixed)).trans active⟩

end PlaneResearch.PlaneDirtyTriple
