import Research.CircuitDual

namespace PlaneResearch.CircuitDual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem gate_shape (n : ℕ) (g : Gate) :
    ((gate n g).op=.and ∨ (gate n g).op=.or ∨ (gate n g).op=.not) ∧
    (gate n g).inputs.length≤g.inputs.length ∧ ((gate n g).op=.not → g.op=.not) := by
  obtain ⟨op,args⟩ := g
  cases op with
  | and => simp only [gate]; split <;> simp
  | or => exact ⟨Or.inl rfl,List.length_filter_le ..,by simp [gate]⟩
  | not =>
    cases args with
    | nil => simp [gate]
    | cons i tail => simp only [gate]; split <;> simp
  | mod m => simp [gate]
  | maj => simp [gate]

theorem fanin (C : Circuit) (n : ℕ) (ok : FanInTwo C) : FanInTwo (circuit n C) := by
  obtain ⟨gs,out⟩ := C
  change ∀ g ∈ gates n gs, _ at ⊢
  induction gs generalizing n with
  | nil => simp [gates]
  | cons g gs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|mem
    · exact ⟨(gate_shape n g).1,(gate_shape n g).2.1.trans (ok g List.mem_cons_self).2⟩
    · exact ih (n+1) (fun h hh => ok h (List.mem_cons_of_mem _ hh)) _ mem

theorem monotone (C : Circuit) (n : ℕ) (ok : Monotone2 C) : Monotone2 (circuit n C) := by
  obtain ⟨gs,out⟩ := C
  change ∀ g ∈ gates n gs, _ at ⊢
  induction gs generalizing n with
  | nil => simp [gates]
  | cons g gs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|mem
    · obtain ⟨allowed,ar⟩ := ok g List.mem_cons_self
      have shape := gate_shape n g
      refine ⟨?_,shape.2.1.trans ar⟩
      rcases shape.1 with yes|yes|no
      · exact Or.inl yes
      · exact Or.inr yes
      · have nold := shape.2.2 no
        rcases allowed with a|o <;> simp_all
    · exact ih (n+1) (fun h hh => ok h (List.mem_cons_of_mem _ hh)) _ mem

theorem not_at (n : ℕ) (gs : List Gate) (k : ℕ) (bound : k<gs.length)
    (hit : ((gates n gs)[k]'(by rwa [length_gates])).op=.not) : (gs[k]).op=.not := by
  induction gs generalizing n k with
  | nil => simp at bound
  | cons g gs ih =>
    cases k with
    | zero => exact (gate_shape n g).2.2 hit
    | succ k => exact ih (n+1) k (by simpa using bound) hit

def AtMostOne (gs : List Gate) := ∀ i j : Fin gs.length,
  (gs.get i).op=.not → (gs.get j).op=.not → i=j

theorem one (n : ℕ) (gs : List Gate) (ok : AtMostOne gs) : AtMostOne (gates n gs) := by
  intro i j ni nj
  have hi : i.val<gs.length := (length_gates n gs) ▸ i.isLt
  have hj : j.val<gs.length := (length_gates n gs) ▸ j.isLt
  exact Fin.ext (congrArg (fun p : Fin gs.length => p.val) (ok ⟨i.val,hi⟩ ⟨j.val,hj⟩
    (not_at n gs i.val hi ni) (not_at n gs j.val hj nj)))

theorem size (n : ℕ) (C : Circuit) : (circuit n C).size=C.size := length_gates n C.gates

end PlaneResearch.CircuitDual
