import Research.PlaneOrderThree
import Research.FiveRowsOr

namespace PlaneResearch.PlaneOrderThree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.Projection PlaneResearch.InputDegree
open PlaneResearch.ParameterOr

private lemma row4 : ∀ i, (lines i).card = 4 := by decide +kernel
private lemma lineThin : ∀ i j, i ≠ j → (lines i ∩ lines j).card ≤ 1 := by decide +kernel

private lemma two_holes : ∀ a b : Fin 13, a ≠ b → ∃ j, a ∈ lines j ∧ b ∈ lines j ∧
    ∀ p ∉ lines j, (Finset.univ.filter (fun k => p ∈ lines k ∧ a ∉ lines k ∧ b ∉ lines k)).card ≤ 2 := by
  decide +kernel

/-- The six projective lines avoiding two distinct points require 18 shared gates
even with unrestricted negation. The holes parameterize all 78 grids. -/
theorem six_avoiding_two (a b : Fin 13) (ab : a ≠ b) (lab : Fin 6 ↪ Fin 13)
    (misses : ∀ i, a ∉ lines (lab i) ∧ b ∉ lines (lab i))
    (C : Circuit) (out : Fin 6 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (lines (lab i)) x) :
    18 ≤ C.size := by
  classical
  obtain ⟨j,aj,_,cap⟩ := two_holes a b ab
  let S (i : Fin 6) := lines (lab i)
  let U (k : Fin 13) := if a ∉ lines k ∧ b ∉ lines k then lines k else ∅
  have thinS (i k) (ik : i ≠ k) : (S i ∩ S k).card ≤ 1 := lineThin _ _ (fun eq => ik (lab.injective eq))
  have sub (i : Fin 6) : S i ⊆ U (lab i) := by simp [S,U,misses i]
  have low (p) (hp : p ∉ lines j) : degree S p ≤ 2 := by
    apply (subdegree U S lab lab.injective sub p).trans
    have same : (Finset.univ.filter (fun k => p ∈ U k)) =
        Finset.univ.filter (fun k => p ∈ lines k ∧ a ∉ lines k ∧ b ∉ lines k) := by
      ext k
      by_cases e : a ∉ lines k ∧ b ∉ lines k <;> simp [U,e]
    simpa only [degree,same] using cap p hp
  have one (i : Fin 6) : (S i ∩ lines j).card ≤ 1 :=
    lineThin _ _ (fun eq => (misses i).1 (eq ▸ aj))
  have h := one_high_per_row S (lines j) thinS low one C out hf hc
  simpa [S,row4] using h

def avoiding (H : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun k => Disjoint (lines k) H)

private lemma recover : ∀ a b : Fin 13, a ≠ b →
    (avoiding {a,b}).biUnion lines = Finset.univ \ {a,b} := by decide +kernel

theorem six_retained : ∀ a b : Fin 13, a ≠ b → (avoiding {a,b}).card = 6 := by decide +kernel

/-- Distinct pairs of holes produce 78 distinct six-line subfamilies. -/
theorem number_of_grids :
    (((Finset.univ : Finset (Fin 13)).powersetCard 2).image avoiding).card = 78 := by
  have inv (s : Finset (Fin 13)) (h : s ∈ Finset.univ.powersetCard 2) :
      (avoiding s).biUnion lines = Finset.univ \ s := by
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp h).2
    exact recover a b ab
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard]; decide
  · intro x hx y hy eq
    have complements := congrArg (fun I : Finset (Fin 13) => I.biUnion lines) eq
    rw [inv x hx,inv y hy] at complements
    ext p
    have mem := Finset.ext_iff.mp complements p
    exact not_iff_not.mp (by simpa using mem)

theorem all_five_lines (lab : Fin 5 ↪ Fin 13) (C : Circuit) (out : Fin 5 → ℕ) (hf : FanInTwo C)
    (hc : ∀ i x, (Circuit.mk C.gates (out i)).eval (List.ofFn x) = sumRow (lines (lab i)) x) :
    15 ≤ C.size := by
  have h := five_rows (by decide : 5 ≤ 5) (fun i => lines (lab i)) (fun i => by rw [row4]; decide)
    (fun i j ne => lineThin _ _ (fun eq => ne (lab.injective eq))) C out hf hc
  simpa [row4] using h

end PlaneResearch.PlaneOrderThree
