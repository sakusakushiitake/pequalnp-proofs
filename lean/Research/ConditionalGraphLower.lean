import Research.CleanLower
import PEqualNP.Defs.CoverPromise
import PEqualNP.Defs.MetaComplexityLgpMono

namespace PlaneResearch.ConditionalGraphLower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.StarOwners
open PlaneResearch.BicliqueStar PlaneResearch.CleanWireModel PlaneResearch.TripleSystems

/-- The edge-count plus cover lower bound with the additional independent
pair condition on AND gates. The circuit operations, graph cover predicate,
and edge cardinality are the ones used in the posted general problem. -/
theorem bound {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (non : ∃ u v, G.Adj u v)
    (square : ∀ a b c d : Fin n, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a)
    (covers : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t≤S.card)
    (mono : Monotone2 C) (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔
      ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) (clean : PairClean G C) :
    G.edgeSet.ncard+t≤C.size+1 := by
  classical
  obtain ⟨u,v,uv⟩ := non
  letI : Nonempty (Fin n) := ⟨u⟩
  have sq : NoSquare G := by
    intro a b c d ab bc cd da
    by_cases same : a=c
    · exact Or.inl same
    · right
      by_contra bd
      exact square a b c d ab.ne same da.ne.symm bc.ne bd cd.ne ab bc cd da
  have off (p : Fin n) : W C C.output (single p)=false := by
    apply Bool.eq_false_iff.mpr
    intro on'
    obtain ⟨a,b,h,aa,bb⟩ := (correct _).mp on'
    have ea : a=p := of_decide_eq_true aa
    have eb : b=p := of_decide_eq_true bb
    exact G.loopless.irrefl p (by simpa only [ea,eb] using h)
  have on' (p q : Fin n) (h : G.Adj p q) : W C C.output (pair p q)=true :=
    (correct _).mpr ⟨p,q,h,by simp [pair],by simp [pair]⟩
  have valid : C.output<n+C.gates.length := by
    by_contra! out
    have yes := on' u v uv
    change (wiresFrom C.gates (List.ofFn (pair u v))).getD C.output false=true at yes
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using out)] at yes
    contradiction
  let o : Node n C := ⟨C.output,valid⟩
  obtain ⟨K,hK,price⟩ := clean_lower G sq C o
    (fun g h => by simpa using (mono g h).1) (fun g h => (mono g h).2) clean off on'
  have count : G.edgeSet.ncard=G.edgeFinset.card := by
    rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have cover := covers K hK
  change G.edgeSet.ncard+t≤C.gates.length+1
  omega

end PlaneResearch.ConditionalGraphLower
