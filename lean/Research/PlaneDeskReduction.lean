import Research.PlaneSearchReduction

namespace PlaneResearch.PlaneDeskReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.PlaneClean PlaneResearch.PlaneProbeOrbit
open PlaneResearch.PlaneDirtyTriple PlaneResearch.CleanProbeFamily

private def ordered : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
private theorem entries : ∀ u v : V, (u.val,v.val) ∈ ordered ↔ (u,v) ∈ edges := by decide +kernel
private theorem mono (C : Circuit) : Monotone2 C ↔ Mono C := by
  simp [Monotone2,Mono]
private theorem recorded (C : Circuit) :
    (∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
      ∃ p q : V, (p.val,q.val) ∈ ordered ∧ x p=true ∧ x q=true) ↔ Correct C := by
  constructor
  · intro left x
    rw [left]
    constructor
    · rintro ⟨p,q,pq,hp,hq⟩
      exact ⟨p,q,Or.inl ((entries p q).mp pq),hp,hq⟩
    · rintro ⟨p,q,pq,hp,hq⟩
      rcases pq with f|b
      · exact ⟨p,q,(entries p q).mpr f,hp,hq⟩
      · exact ⟨q,p,(entries q p).mpr b,hq,hp⟩
  · intro right x
    rw [right]
    constructor
    · rintro ⟨p,q,pq,hp,hq⟩
      rcases pq with f|b
      · exact ⟨p,q,(entries p q).mpr f,hp,hq⟩
      · exact ⟨q,p,(entries q p).mpr b,hq,hp⟩
    · rintro ⟨p,q,pq,hp,hq⟩
      exact ⟨p,q,Or.inl ((entries p q).mp pq),hp,hq⟩

/-- The left-hand side is the desk statement itself. A size-preserving
renaming allows one additional necessary AND test on the right-hand side. -/
theorem desk_iff :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ↔
    ∃ C : Circuit, Mono C ∧ C.size≤63 ∧ Correct C ∧ Fires C (indicator fixed) := by
  rw [←PlaneResearch.PlaneSearchReduction.exists_iff_fixed]
  apply exists_congr
  intro C
  exact and_congr (mono C) (and_congr_right (fun _ => recorded C))

end PlaneResearch.PlaneDeskReduction
