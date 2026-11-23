import Mathlib

namespace CoverTreeResearch

abbrev State (n : ℕ) := Fin n → Option Bool
def ones {n : ℕ} (s : State n) : Finset (Fin n) := Finset.univ.filter (fun i => s i=some true)
def free {n : ℕ} (s : State n) : Finset (Fin n) := Finset.univ.filter (fun i => s i=none)
def NoBad {n : ℕ} (G : SimpleGraph (Fin n)) (s : State n) :=
  ¬ ∃ u v, G.Adj u v ∧ s u=some false ∧ s v=some false
def Valid {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) (N : State n → ℕ) :=
  ∀ s, (((∃ u v, G.Adj u v ∧ s u=some false ∧ s v=some false) ∨
           ∃ T : Finset (Fin n), T.card=t ∧ ∀ i ∈ T, s i=some true) ∧ 1≤N s) ∨
    ∃ y, s y=none ∧ N (Function.update s y (some false))+N (Function.update s y (some true))≤N s

lemma free_update {n : ℕ} (s : State n) (y : Fin n) (b : Bool) :
    free (Function.update s y (some b)) = (free s).erase y := by
  ext i
  by_cases eq : i=y <;> simp [free,Function.update,eq]

lemma ones_on {n : ℕ} (s : State n) (y : Fin n) :
    ones (Function.update s y (some true)) = insert y (ones s) := by
  ext i
  by_cases eq : i=y <;> simp [ones,Function.update,eq]

lemma ones_off {n : ℕ} (s : State n) {y : Fin n} (un : s y=none) :
    ones (Function.update s y (some false)) = ones s := by
  ext i
  by_cases eq : i=y
  · subst i; simp [ones,un]
  · simp [ones,Function.update,eq]

lemma pos {n t : ℕ} (G : SimpleGraph (Fin n)) (N : State n → ℕ) (ok : Valid G t N) :
    ∀ s, 1≤N s := by
  suffices main : ∀ k s, (free s).card=k → 1≤N s from fun s => main _ s rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro s eq
    rcases ok s with leaf|⟨y,un,add⟩
    · exact leaf.2
    · have mem : y ∈ free s := by simp [free,un]
      have lt : (free (Function.update s y (some false))).card<k := by
        rw [free_update,←eq]
        exact Finset.card_erase_lt_of_mem mem
      have := ih _ lt _ rfl
      omega

lemma branch {n t : ℕ} {G : SimpleGraph (Fin n)} {N : State n → ℕ} (ok : Valid G t N)
    {s : State n} (safe : NoBad G s) (few : (ones s).card<t) :
    ∃ y, s y=none ∧ N (Function.update s y (some false))+N (Function.update s y (some true))≤N s := by
  rcases ok s with ⟨bad|⟨T,ht,inc⟩,_⟩|node
  · exact (safe bad).elim
  · have sub : T ⊆ ones s := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc i hi⟩
    have := Finset.card_le_card sub
    omega
  · exact node

lemma safe_on {n : ℕ} {G : SimpleGraph (Fin n)} {s : State n} (safe : NoBad G s) (y : Fin n) :
    NoBad G (Function.update s y (some true)) := by
  rintro ⟨u,v,edge,hu,hv⟩
  have prior (i : Fin n) (h : Function.update s y (some true) i=some false) : s i=some false := by
    by_cases eq : i=y
    · simp [eq] at h
    · simpa [Function.update,eq] using h
  exact safe ⟨u,v,edge,prior u hu,prior v hv⟩

theorem chain_lower {n t : ℕ} (G : SimpleGraph (Fin n)) (N : State n → ℕ) (ok : Valid G t N) :
    ∀ k s, (ones s).card+k=t → NoBad G s → k+1≤N s := by
  intro k
  induction k with
  | zero => intro s _ _; exact pos G N ok s
  | succ k ih =>
    intro s gap safe
    obtain ⟨y,un,add⟩ := branch ok safe (by omega)
    have miss : y ∉ ones s := by simp [ones,un]
    have up : (ones (Function.update s y (some true))).card=(ones s).card+1 := by
      rw [ones_on,Finset.card_insert_of_notMem miss]
    have yes := ih _ (by omega) (safe_on safe y)
    have no := pos G N ok (Function.update s y (some false))
    omega

theorem triangular_lower {n t : ℕ} (G : SimpleGraph (Fin n)) (N : State n → ℕ) (ok : Valid G t N) :
    ∀ k s, (ones s).card+k=t → (∀ i, s i ≠ some false) → (k+1)*(k+2)≤2*N s := by
  intro k
  induction k with
  | zero =>
    intro s _ _
    have := pos G N ok s
    omega
  | succ k ih =>
    intro s gap allpos
    have safe : NoBad G s := fun ⟨u,_,_,hu,_⟩ => allpos u hu
    obtain ⟨y,un,add⟩ := branch ok safe (by omega)
    have miss : y ∉ ones s := by simp [ones,un]
    have up : (ones (Function.update s y (some true))).card=(ones s).card+1 := by
      rw [ones_on,Finset.card_insert_of_notMem miss]
    have stays (i : Fin n) : Function.update s y (some true) i ≠ some false := by
      by_cases eq : i=y
      · simp [eq]
      · simpa [Function.update,eq] using allpos i
    have down : NoBad G (Function.update s y (some false)) := by
      rintro ⟨a,b,edge,ha,hb⟩
      have only (i : Fin n) (h : Function.update s y (some false) i=some false) : i=y := by
        by_contra ne
        exact allpos i (by simpa [Function.update,ne] using h)
      exact edge.ne ((only a ha).trans (only b hb).symm)
    have yes := ih _ (by omega) stays
    have no := chain_lower G N ok (k+1) (Function.update s y (some false))
      (by rw [ones_off s un]; omega) down
    nlinarith only [add,yes,no]

end CoverTreeResearch
