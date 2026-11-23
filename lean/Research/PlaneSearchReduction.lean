import Research.PlaneDirtyTriple
import Research.PlaneCleanBound

namespace PlaneResearch.PlaneSearchReduction
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.TripleSystems
open PlaneResearch.CleanWireModel PlaneResearch.CleanProbeFamily
open PlaneResearch.PlaneClean PlaneResearch.PlaneProbeOrbit PlaneResearch.PlaneDirtyTriple

private lemma pair_independent (p q : V) (no : ¬adjacent p q) : Independent graph {p,q} := by
  intro a ha b hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact graph.loopless.irrefl _
  · exact no
  · exact fun h => no (Or.symm h)
  · exact graph.loopless.irrefl _

lemma response (C : Circuit) (hc : Correct C) :
    (∀ p : V, W C C.output (single p)=false) ∧
      ∀ p q : V, adjacent p q → W C C.output (pair p q)=true := by
  constructor
  · intro p
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨a,b,ab,aa,bb⟩ := (hc (single p)).mp yes
    have aeq : a=p := of_decide_eq_true aa
    have beq : b=p := of_decide_eq_true bb
    have loop : adjacent p p := by simpa only [aeq,beq] using ab
    exact graph.loopless.irrefl p loop
  · intro p q pq
    exact (hc _).mpr ⟨p,q,pq,by simp [pair],by simp [pair]⟩

lemma output_in_range (C : Circuit) (hc : Correct C) : C.output<26+C.gates.length := by
  by_contra! out
  have edge := (response C hc).2 0 13 (by decide +kernel)
  change (wiresFrom C.gates (List.ofFn (pair (0 : V) 13))).getD C.output false=true at edge
  rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using out)] at edge
  contradiction

/-- In the assigned 26-vertex graph any circuit of size at most 63 that
computes the edge function has an AND firing on an independent input. -/
theorem dirty_required (C : Circuit) (hm : Mono C) (hc : Correct C) (small : C.size≤63) :
    ∃ S : Finset V, Independent graph S ∧ Fires C (indicator S) := by
  classical
  by_contra! no
  have clean : PairClean graph C := by
    intro k hk op p q on'
    by_contra miss
    have eq : indicator ({p,q} : Finset V)=pair p q := funext (fun i => by simp [indicator,pair])
    exact no {p,q} (pair_independent p q miss)
      ⟨k,C.gates[k],List.getElem?_eq_getElem hk,op,eq ▸ on'⟩
  obtain ⟨off,on'⟩ := response C hc
  let o : Node 26 C := ⟨C.output,output_in_range C hc⟩
  have lower := PlaneResearch.PlaneCleanBound.at_least_64 C o (fun g h => (hm g h).1)
    (fun g h => (hm g h).2) clean off on'
  omega

/-- Exact existential reduction, with a single fixed independent test. -/
theorem exists_iff_fixed :
    (∃ C : Circuit, Mono C ∧ C.size≤63 ∧ Correct C) ↔
    ∃ C : Circuit, Mono C ∧ C.size≤63 ∧ Correct C ∧ Fires C (indicator fixed) := by
  constructor
  · rintro ⟨C,hm,small,hc⟩
    obtain ⟨S,ind,fire⟩ := dirty_required C hm hc small
    obtain ⟨D,correct,mono,eq,dirty⟩ := normalize C hc hm S ind fire
    exact ⟨D,mono,eq ▸ small,correct,dirty⟩
  · rintro ⟨C,hm,small,hc,_⟩
    exact ⟨C,hm,small,hc⟩

end PlaneResearch.PlaneSearchReduction
