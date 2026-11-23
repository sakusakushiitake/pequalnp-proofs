import Research.MonotoneCertificate

namespace PlaneResearch.ElevenDirtyUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.MonotoneCertificate PlaneResearch.StarOwners
abbrev V := Fin 11
def E : List (V × V) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def C : Circuit := ⟨[⟨.or,[5,9]⟩,⟨.or,[0,5]⟩,⟨.or,[2,9]⟩,⟨.and,[13,11]⟩,⟨.and,[12,14]⟩,⟨.or,[0,2]⟩,⟨.and,[10,16]⟩,⟨.or,[10,1]⟩,⟨.and,[4,18]⟩,⟨.or,[11,4]⟩,⟨.or,[20,1]⟩,⟨.and,[8,21]⟩,⟨.or,[3,10]⟩,⟨.and,[6,23]⟩,⟨.or,[6,9]⟩,⟨.or,[25,3]⟩,⟨.and,[7,26]⟩,⟨.or,[19,15]⟩,⟨.or,[22,27]⟩,⟨.or,[29,28]⟩,⟨.or,[17,24]⟩,⟨.or,[31,30]⟩],32⟩
private def certificate : List (Terms 11) := [[{5},{9}],[{0},{5}],[{2},{9}],[{2,5},{9}],[{2,5},{0,9},{5,9}],[{0},{2}],[{0,10},{2,10}],[{1},{10}],[{1,4},{4,10}],[{4},{5},{9}],[{1},{4},{5},{9}],[{1,8},{4,8},{5,8},{8,9}],[{3},{10}],[{3,6},{6,10}],[{6},{9}],[{3},{6},{9}],[{3,7},{6,7},{7,9}],[{1,4},{2,5},{0,9},{5,9},{4,10}],[{3,7},{6,7},{1,8},{4,8},{5,8},{7,9},{8,9}],[{1,4},{2,5},{3,7},{6,7},{1,8},{4,8},{5,8},{0,9},{5,9},{7,9},{8,9},{4,10}],[{3,6},{0,10},{2,10},{6,10}],[{1,4},{2,5},{3,6},{3,7},{6,7},{1,8},{4,8},{5,8},{0,9},{5,9},{7,9},{8,9},{0,10},{2,10},{4,10},{6,10}]]
theorem size : C.size=22 := by decide +kernel
theorem monotone : Monotone2 C := monotone_checked C (by decide +kernel)
private theorem checked : ∀ k : Fin C.gates.length,
    checkGate certificate k.val (C.gates.get k)=true := by decide +kernel
private theorem final_terms : same (atWire certificate C.output) (edgeTerms E)=true := by decide +kernel
theorem correct (x : V → Bool) : C.eval (List.ofFn x)=true ↔
    ∃ p q, (p,q) ∈ E ∧ x p=true ∧ x q=true :=
  (wire C certificate checked x C.output (by decide +kernel)).trans ((equiv final_terms x).trans (edges E x))

/-- A binary AND inside the explicit correct circuit fires on a singleton. -/
theorem dirty_singleton : (C.gates.get ⟨3,by decide⟩).op=.and ∧ W C (11+3) (single (9:V))=true := ⟨rfl,by decide +kernel⟩

end PlaneResearch.ElevenDirtyUpper
