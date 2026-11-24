import PEqualNP.MetaComplexity.Helpers.Support

namespace PlaneResearch.BinarySupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
variable {n : ℕ}

def trim (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not,g.inputs.take 1⟩
  | _ => g

def cost (g : Gate) : ℕ := match g.op with | .not => 0 | _ => 1

lemma trim_value (g : Gate) (w : List Bool) :
    (trim g).op.eval ((trim g).inputs.map fun i => w.getD i false)=
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op,ls⟩ := g
  cases op <;> cases ls <;> rfl

lemma trim_wires (gs : List Gate) (w : List Bool) : wiresFrom (gs.map trim) w=wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom (gs.map trim) (w++[_])=wiresFrom gs (w++[_])
    rw [ih,trim_value]

-- This is the support-count argument of PEqualNP.MetaComplexity.Helpers.Support,
-- with the original unit charge replaced by the actual increase in frontier size.
lemma cost_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length≤2)
    (h : Cnt t L) : Cnt (t+cost g) (L++[gateSupp L (trim g)]) := by
  have ar : (trim g).inputs.length≤1+cost g := by
    obtain ⟨op,ls⟩ := g
    cases op <;> simp_all [trim,cost]
  intro W
  let reads := (trim g).inputs.toFinset
  by_cases hW : L.length ∈ W
  · have sub : (W.biUnion fun j => (L++[gateSupp L (trim g)]).getD j ∅) ⊆
        ((W.erase L.length ∪ reads).biUnion fun j => L.getD j ∅) := by
      intro i hi
      obtain ⟨j,hj,hit⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j=L.length
      · subst j
        rw [getD_snoc_eq] at hit
        obtain ⟨a,ha,mem⟩ := (mem_gateSupp L (trim g) i).mp hit
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_right _ (List.mem_toFinset.mpr ha),mem⟩
      · rw [getD_snoc_ne _ _ _ _ eq] at hit
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩),hit⟩
    have rsize : reads.card≤1+cost g := (List.toFinset_card_le _).trans ar
    have spread := Finset.card_union_le (W.erase L.length) reads
    rw [Finset.card_erase_of_mem hW] at spread
    have positive := Finset.card_pos.mpr ⟨_,hW⟩
    have := h (W.erase L.length ∪ reads)
    have := Finset.card_le_card sub
    omega
  · have eq : (W.biUnion fun j => (L++[gateSupp L (trim g)]).getD j ∅)=
        (W.biUnion fun j => L.getD j ∅) :=
      Finset.biUnion_congr rfl (fun j hj => getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj)))
    rw [eq]
    have := h W
    omega

theorem cost_all (gs : List Gate) : ∀ t (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length≤2) → Cnt t L →
    Cnt (t+(gs.map cost).sum) (suppsFrom (gs.map trim) L) := by
  induction gs with
  | nil => intro t L _ h; simpa [suppsFrom] using h
  | cons g gs ih =>
    intro t L ar h
    have next := ih (t+cost g) (L++[gateSupp L (trim g)])
      (fun a ha => ar a (List.mem_cons_of_mem _ ha)) (cost_step t L g (ar g List.mem_cons_self) h)
    simpa [suppsFrom,add_assoc] using next

theorem essential_inputs (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length≤2)
    (sensitive : ∀ i : Fin n, ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x i (!(x i)))) ≠ C.eval (List.ofFn x)) :
    n≤(C.gates.map cost).sum+1 := by
  let gs := C.gates.map trim
  let S := (suppsFrom gs (inputSupps n)).getD C.output ∅
  have all (i : Fin n) : i ∈ S := by
    by_contra absent
    obtain ⟨x,hx⟩ := sensitive i
    apply hx
    have eq := (agree_wiresFrom (Function.update x i (!(x i))) x gs _ _ _ (agree_inputs _ _)).2.2 C.output
      (fun j hj => by
        have ne : j ≠ i := fun same => absent (same ▸ hj)
        simp [Function.update,ne])
    change (wiresFrom C.gates (List.ofFn (Function.update x i (!(x i))))).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    simpa only [gs,trim_wires] using eq
  have card : S.card=n := by rw [Finset.eq_univ_of_forall all]; simp
  have bound := cost_all C.gates 0 (inputSupps n) arity cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at bound
  exact card ▸ bound

end PlaneResearch.BinarySupport
