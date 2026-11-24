import Research.CircuitDualSize

namespace PlaneResearch.CircuitDual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.TripleSystems (wiresFrom length_wiresFrom)
variable {n : ℕ}

def flip (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) := !(f (fun i => !(x i)))
def Computes (C : Circuit) (f : (Fin n → Bool) → Bool) := ∀ x, C.eval (List.ofFn x)=f x

theorem flip_flip (f : (Fin n → Bool) → Bool) : flip (flip f)=f := by
  funext x
  simp [flip]

lemma output_valid {C : Circuit} {f : (Fin n → Bool) → Bool} (ev : Computes C f)
    (on : ∃ x, f x=true) : C.output<n+C.size := by
  obtain ⟨x,yes⟩ := on
  by_contra! bad
  have len : (wiresFrom C.gates (List.ofFn x)).length=n+C.size := by simp [length_wiresFrom,Circuit.size]
  have value := ev x
  change (wiresFrom C.gates (List.ofFn x)).getD C.output false=f x at value
  rw [List.getD_eq_default _ _ (len ▸ bad),yes] at value
  cases value

theorem computes_flip {C : Circuit} {f : (Fin n → Bool) → Bool} (ev : Computes C f)
    (ok : FanInTwo C) (on : ∃ x, f x=true) : Computes (circuit n C) (flip f) := by
  intro x
  let y := fun i => !(x i)
  have valid := output_valid ev on
  have h := dual_eval C (List.ofFn y) ok (by simpa using valid)
  have back : (List.ofFn y).map (!·)=List.ofFn x := by simp [List.map_ofFn,y,Function.comp_def]
  rw [back,List.length_ofFn,ev y] at h
  exact h

def SmallOne (f : (Fin n → Bool) → Bool) (k : ℕ) :=
  ∃ C : Circuit, C.size≤k ∧ FanInTwo C ∧ AtMostOne C.gates ∧ Computes C f
def SmallMon (f : (Fin n → Bool) → Bool) (k : ℕ) :=
  ∃ C : Circuit, C.size≤k ∧ Monotone2 C ∧ Computes C f

theorem transport_one {f : (Fin n → Bool) → Bool} {k : ℕ} (on : ∃ x, f x=true)
    (h : SmallOne f k) : SmallOne (flip f) k := by
  obtain ⟨C,cap,ok,neg,ev⟩ := h
  exact ⟨circuit n C,(size n C) ▸ cap,fanin C n ok,one n C.gates neg,computes_flip ev ok on⟩

theorem transport_mon {f : (Fin n → Bool) → Bool} {k : ℕ} (on : ∃ x, f x=true)
    (h : SmallMon f k) : SmallMon (flip f) k := by
  obtain ⟨C,cap,ok,ev⟩ := h
  have general : FanInTwo C := fun g hg => ⟨(ok g hg).1.imp_right Or.inl,(ok g hg).2⟩
  exact ⟨circuit n C,(size n C) ▸ cap,monotone C n ok,computes_flip ev general on⟩

lemma flip_on {f : (Fin n → Bool) → Bool} (off : ∃ x, f x=false) : ∃ y, flip f y=true := by
  obtain ⟨x,h⟩ := off
  exact ⟨fun i => !(x i),by simp [flip,h]⟩

theorem one_iff {f : (Fin n → Bool) → Bool} (k : ℕ) (on : ∃ x, f x=true) (off : ∃ x, f x=false) :
    SmallOne f k ↔ SmallOne (flip f) k :=
  ⟨transport_one on,fun h => flip_flip f ▸ transport_one (flip_on off) h⟩
theorem mon_iff {f : (Fin n → Bool) → Bool} (k : ℕ) (on : ∃ x, f x=true) (off : ∃ x, f x=false) :
    SmallMon f k ↔ SmallMon (flip f) k :=
  ⟨transport_mon on,fun h => flip_flip f ▸ transport_mon (flip_on off) h⟩

end PlaneResearch.CircuitDual
