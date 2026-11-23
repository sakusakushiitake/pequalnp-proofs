import Research.CoverTreeLower

namespace CoverTreeResearch

def Terminal {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) (s : State n) :=
  (∃ u v, G.Adj u v ∧ s u=some false ∧ s v=some false) ∨
    ∃ T : Finset (Fin n), T.card=t ∧ ∀ i ∈ T, s i=some true

variable {n t : ℕ} {G : SimpleGraph (Fin n)}
abbrev Feasible (G : SimpleGraph (Fin n)) (t : ℕ) := ∃ N, Valid G t N

private lemma has_cost (f : Feasible G t) (s : State n) : ∃ k, ∃ N, Valid G t N ∧ N s=k := by
  obtain ⟨N,h⟩ := f
  exact ⟨_,N,h,rfl⟩

noncomputable def optimum (f : Feasible G t) (s : State n) : ℕ := by
  classical
  exact Nat.find (has_cost f s)

lemma attains (f : Feasible G t) (s : State n) : ∃ N, Valid G t N ∧ N s=optimum f s := by
  classical
  exact Nat.find_spec (has_cost f s)

lemma least (f : Feasible G t) {N : State n → ℕ} (ok : Valid G t N) (s : State n) :
    optimum f s ≤ N s := by
  classical
  exact Nat.find_min' (has_cost f s) ⟨N,ok,rfl⟩

theorem optimum_valid (f : Feasible G t) : Valid G t (optimum f) := by
  intro s
  obtain ⟨N,ok,eq⟩ := attains f s
  rcases ok s with ⟨done,pos⟩|⟨y,un,add⟩
  · exact Or.inl ⟨done,eq ▸ pos⟩
  · exact Or.inr ⟨y,un,eq ▸ (Nat.add_le_add (least f ok _) (least f ok _)).trans add⟩

private lemma improve (f : Feasible G t) (s : State n) (v : ℕ)
    (step : (Terminal G t s ∧ 1≤v) ∨
      ∃ y, s y=none ∧ optimum f (Function.update s y (some false))+
        optimum f (Function.update s y (some true))≤v) : optimum f s≤v := by
  classical
  let M (r : State n) := if r=s then min v (optimum f r) else optimum f r
  have le (r) : M r≤optimum f r := by
    by_cases z : r=s <;> simp [M,z]
  have ok : Valid G t M := by
    intro r
    have old := optimum_valid f r
    by_cases charge : r=s ∧ v<optimum f s
    · obtain ⟨rfl,lt⟩ := charge
      have root : M r=v := by simp [M,Nat.min_eq_left lt.le]
      rcases step with ⟨done,pos⟩|⟨y,un,add⟩
      · exact Or.inl ⟨done,root ▸ pos⟩
      · exact Or.inr ⟨y,un,root ▸ (Nat.add_le_add (le _) (le _)).trans add⟩
    · have root : M r=optimum f r := by
        by_cases eq : r=s
        · subst r
          have h : optimum f s≤v := by
            by_contra! lt
            exact charge ⟨rfl,lt⟩
          simp [M,Nat.min_eq_right h]
        · simp [M,eq]
      rcases old with ⟨done,pos⟩|⟨y,un,add⟩
      · exact Or.inl ⟨done,root ▸ pos⟩
      · exact Or.inr ⟨y,un,root ▸ (Nat.add_le_add (le _) (le _)).trans add⟩
  have small := least f ok s
  have bound : M s≤v := by simp [M]
  exact small.trans bound

theorem optimum_leaf (f : Feasible G t) {s : State n} (done : Terminal G t s) :
    optimum f s=1 :=
  Nat.le_antisymm (improve f s 1 (Or.inl ⟨done,by decide⟩)) (pos G _ (optimum_valid f) s)

theorem optimum_split (f : Feasible G t) {s : State n} {y : Fin n} (un : s y=none) :
    optimum f s ≤ optimum f (Function.update s y (some false))+optimum f (Function.update s y (some true)) :=
  improve f s _ (Or.inr ⟨y,un,le_rfl⟩)

theorem feasible_of_total (total : ∀ s, (∀ i, s i ≠ none) → Terminal G t s) : Feasible G t := by
  classical
  refine ⟨fun s => 2^(free s).card,?_⟩
  intro s
  by_cases present : (free s).Nonempty
  · obtain ⟨y,hy⟩ := present
    have un : s y=none := (Finset.mem_filter.mp hy).2
    refine Or.inr ⟨y,un,?_⟩
    change 2^(free (Function.update s y (some false))).card+
      2^(free (Function.update s y (some true))).card≤2^(free s).card
    rw [free_update,free_update,←Finset.card_erase_add_one hy,pow_succ]
    omega
  · left
    refine ⟨total s (fun i hi => present ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩),?_⟩
    exact Nat.one_le_two_pow

end CoverTreeResearch
