import Research.CleanWireModel
import Research.StarCounting

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.StarCounting

noncomputable def zeros {n : ℕ} (C : Circuit) (o : Node n C) : Finset (Node n C) := by
  classical
  exact (live C o).filter (fun w => support C w=∅)
noncomputable def mixed {n : ℕ} (C : Circuit) (o : Node n C) : Finset (Node n C) := by
  classical
  exact (live C o).filter (fun w => (support C w).Nonempty ∧ ∃ p ∈ parents C w, support C p=∅)

private lemma mixed_capacity {n : ℕ} (C : Circuit) (o w : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (quiet : NoSingletonAnd (n:=n) C) (hw : w ∈ mixed C o) :
    (parents C w ∩ zeros C o).card≤1 := by
  classical
  obtain ⟨_,pos,p,hp,_⟩ := Finset.mem_filter.mp hw
  obtain ⟨_,k,g,eq,hg,_⟩ := (mem_parents C w p).mp hp
  obtain ⟨hk,geq⟩ := List.getElem?_eq_some_iff.mp hg
  have ew : w=node C k hk := Fin.ext eq
  have somePos : ∃ q ∈ parents C w, (support C q).Nonempty := by
    rcases ops C.gates[k] (List.getElem_mem ..) with a|b
    · rw [ew,and_set C quiet k hk a] at pos
      exact (Finset.not_nonempty_empty pos).elim
    · obtain ⟨v,hv⟩ := pos
      rw [ew,or_set C k hk b] at hv
      obtain ⟨q,parent,mem⟩ := Finset.mem_biUnion.mp hv
      exact ⟨q,ew ▸ parent,⟨v,mem⟩⟩
  obtain ⟨q,hq,positive⟩ := somePos
  have strict : parents C w ∩ zeros C o ⊂ parents C w := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left,?_⟩
    intro eq
    have inter : q ∈ parents C w ∩ zeros C o := by rw [eq]; exact hq
    have emp := (Finset.mem_filter.mp (Finset.mem_inter.mp inter).2).2
    exact positive.ne_empty emp
  have := Finset.card_lt_card strict
  have := capacity C two w
  omega

/-- Each distinguished empty-support root consumes one gate. All but at
most one force an additional gate distinct from the positive binary unions. -/
theorem gate_budget {n : ℕ} (C : Circuit) (o : Node n C) (A : Finset (Node n C))
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (quiet : NoSingletonAnd (n:=n) C)
    (root : A ⊆ zeros C o) (pos : ∀ w ∈ A, ∀ p ∈ parents C w, (support C p).Nonempty) :
    (forks C o).card + A.card + A.card ≤ C.gates.length + 1 := by
  classical
  let Z := zeros C o
  let M := mixed C o
  let B := forks C o
  have reader (w) (hw : w ∈ Z) :
      w=o ∨ (∃ j ∈ Z \ A, w ∈ parents C j) ∨ ∃ j ∈ M, w ∈ parents C j := by
    obtain ⟨lw,empty⟩ := Finset.mem_filter.mp hw
    rcases has_reader C o w lw with eq|⟨j,lj,hj⟩
    · exact Or.inl eq
    · by_cases z : support C j=∅
      · have nz : j ∉ A := fun ja => (pos j ja w hj).ne_empty empty
        exact Or.inr (Or.inl ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨lj,z⟩,nz⟩,hj⟩)
      · exact Or.inr (Or.inr ⟨j,Finset.mem_filter.mpr ⟨lj,Finset.nonempty_iff_ne_empty.mpr z,w,hj,empty⟩,hj⟩)
  have charge := zero_read_count Z A M root o (parents C) reader
    (fun j _ => (Finset.card_le_card Finset.inter_subset_left).trans (capacity C two j))
    (fun j h => mixed_capacity C o j ops two quiet h)
  have ZM : Disjoint Z M := Finset.disjoint_left.mpr (fun w hz hm =>
    (Finset.mem_filter.mp hm).2.1.ne_empty (Finset.mem_filter.mp hz).2)
  have ZMB : Disjoint (Z ∪ M) B := by
    apply Finset.disjoint_left.mpr
    intro w hm hb
    obtain ⟨_,_,live',all⟩ := Finset.mem_filter.mp hb
    rcases Finset.mem_union.mp hm with hz|hm
    · exact live'.ne_empty (Finset.mem_filter.mp hz).2
    · obtain ⟨_,_,p,hp,emp⟩ := Finset.mem_filter.mp hm
      exact (all p hp).ne_empty emp
  have gates (w) (hw : w ∈ (Z ∪ M) ∪ B) : n≤w.val := by
    rcases Finset.mem_union.mp hw with h|h
    · rcases Finset.mem_union.mp h with hz|hm
      · by_contra! raw
        have emp := (Finset.mem_filter.mp hz).2
        rw [raw_set C w raw] at emp
        simp at emp
      · obtain ⟨_,_,p,hp,_⟩ := Finset.mem_filter.mp hm
        obtain ⟨_,k,_,eq,_,_⟩ := (mem_parents C w p).mp hp
        omega
    · exact (Finset.mem_filter.mp h).2.1
  have bound : ((Z ∪ M) ∪ B).card ≤ (Finset.range C.gates.length).card := by
    apply Finset.card_le_card_of_injOn (fun w : Node n C => w.val-n)
    · intro w hw
      apply Finset.mem_range.mpr
      change w.val - n < C.gates.length
      have := w.isLt
      have := gates w hw
      omega
    · intro w hw v hv eq
      apply Fin.ext
      have := gates w hw
      have := gates v hv
      change w.val-n=v.val-n at eq
      omega
  rw [Finset.card_union_of_disjoint ZMB,Finset.card_union_of_disjoint ZM,Finset.card_range] at bound
  have total := Finset.card_sdiff_add_card_eq_card (show A ⊆ Z from root)
  change B.card+A.card+A.card ≤ _
  omega

end PlaneResearch.CleanWireModel
