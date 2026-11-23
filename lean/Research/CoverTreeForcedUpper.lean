import Research.CoverTreeUpper

namespace CoverTreeResearch
variable {n t : ℕ} {G : SimpleGraph (Fin n)}

noncomputable def pending (G : SimpleGraph (Fin n)) (s : State n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => s v=none ∧ ∃ u, G.Adj u v ∧ s u=some false)

lemma pending_mem {s : State n} {v : Fin n} :
    v ∈ pending G s ↔ s v=none ∧ ∃ u, G.Adj u v ∧ s u=some false := by
  classical
  simp [pending]

lemma pending_on {s : State n} {y : Fin n} (un : s y=none) :
    pending G (Function.update s y (some true))=(pending G s).erase y := by
  classical
  ext v
  by_cases vy : v=y
  · simp [vy,pending_mem]
  · have stable (u : Fin n) : Function.update s y (some true) u=some false ↔ s u=some false := by
      by_cases uy : u=y <;> simp [Function.update,uy,un]
    simp [Finset.mem_erase,pending_mem,vy,Function.update_of_ne vy,stable]

theorem pending_chain (miss : Uncovered G t) :
    ∀ k m (s : State n), (ones s).card+k+m=t → k≤(pending G s).card →
      optimum (cover_feasible miss) s+1≤k+2^(m+1) := by
  intro k
  induction k with
  | zero =>
    intro m s bal _
    simpa using exponential_upper miss m s (by omega)
  | succ k ih =>
    intro m s bal enough
    obtain ⟨v,mem⟩ := Finset.card_pos.mp (show 0<(pending G s).card by omega)
    obtain ⟨un,u,edge,off⟩ := pending_mem.mp mem
    have up := on_count un
    have rest : k≤(pending G (Function.update s v (some true))).card := by
      rw [pending_on un]
      have := Finset.card_erase_add_one mem
      omega
    have yes := ih m _ (by omega) rest
    have done : Terminal G t (Function.update s v (some false)) :=
      Or.inl ⟨u,v,edge,by simpa [Function.update,edge.ne] using off,by simp⟩
    have no := optimum_leaf (cover_feasible miss) done
    have node := optimum_split (cover_feasible miss) un
    omega

theorem pending_upper (miss : Uncovered G t) (s : State n) :
    let r := t-(ones s).card
    let b := (pending G s).card
    optimum (cover_feasible miss) s + 1 ≤ min r b + 2^(r-b+1) := by
  dsimp only
  by_cases large : t≤(ones s).card
  · rw [optimum_leaf (cover_feasible miss) (true_leaf G large),Nat.sub_eq_zero_of_le large]
    simp
  · apply pending_chain miss (min (t-(ones s).card) (pending G s).card) _ s
    · omega
    · exact min_le_right .. 

end CoverTreeResearch
