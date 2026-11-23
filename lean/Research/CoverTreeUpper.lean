import Research.CoverTreeOptimum

namespace CoverTreeResearch

abbrev Uncovered {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) :=
  ∀ S : Finset (Fin n), S.card<t → ∃ u v, G.Adj u v ∧ u ∉ S ∧ v ∉ S

lemma true_leaf {n t : ℕ} (G : SimpleGraph (Fin n)) {s : State n} (h : t≤(ones s).card) :
    Terminal G t s := by
  obtain ⟨S,inc,eq⟩ := Finset.exists_subset_card_eq h
  exact Or.inr ⟨S,eq,fun i hi => (Finset.mem_filter.mp (inc hi)).2⟩

lemma inactive {n : ℕ} {s : State n} {i : Fin n} (h : i ∉ ones s) :
    s i=none ∨ s i=some false := by
  cases eq : s i with
  | none => exact Or.inl rfl
  | some b =>
    cases b with
    | false => exact Or.inr rfl
    | true => exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩)).elim

theorem cover_feasible {n t : ℕ} {G : SimpleGraph (Fin n)} (miss : Uncovered G t) : Feasible G t := by
  apply feasible_of_total
  intro s ready
  by_cases h : t≤(ones s).card
  · exact true_leaf G h
  · obtain ⟨u,v,edge,nu,nv⟩ := miss (ones s) (by omega)
    exact Or.inl ⟨u,v,edge,(inactive nu).resolve_left (ready u),(inactive nv).resolve_left (ready v)⟩

lemma on_count {n : ℕ} {s : State n} {y : Fin n} (un : s y=none) :
    (ones (Function.update s y (some true))).card=(ones s).card+1 := by
  rw [ones_on,Finset.card_insert_of_notMem]
  simp [ones,un]

lemma unit_bound {n t k : ℕ} {G : SimpleGraph (Fin n)} (f : Feasible G t)
    (ih : ∀ s, (ones s).card+k=t → optimum f s+1≤2^(k+1))
    {s : State n} (gap : (ones s).card+(k+1)=t) {u v : Fin n}
    (edge : G.Adj u v) (off : s u=some false) (nv : v ∉ ones s) : optimum f s≤2^(k+1) := by
  rcases inactive nv with un|no
  · have term : Terminal G t (Function.update s v (some false)) := Or.inl
      ⟨u,v,edge,by simpa [Function.update,edge.ne] using off,by simp⟩
    have a := optimum_split f un
    have zero := optimum_leaf f term
    have up := on_count un
    have one := ih (Function.update s v (some true)) (by omega)
    omega
  · have eq := optimum_leaf f (show Terminal G t s from Or.inl ⟨u,v,edge,off,no⟩)
    rw [eq]
    exact Nat.one_le_two_pow

theorem exponential_upper {n t : ℕ} {G : SimpleGraph (Fin n)} (miss : Uncovered G t) :
    ∀ k s, (ones s).card+k=t → optimum (cover_feasible miss) s+1≤2^(k+1) := by
  let f := cover_feasible miss
  intro k
  induction k with
  | zero =>
    intro s gap
    rw [optimum_leaf f (true_leaf G (by omega : t≤(ones s).card))]
    decide
  | succ k ih =>
    intro s gap
    obtain ⟨u,v,edge,nu,nv⟩ := miss (ones s) (by omega)
    have pow : 2^(k+1+1) = 2^(k+1)*2 := pow_succ _ _
    rcases inactive nu with un|off
    · have up := on_count un
      have yes := ih (Function.update s u (some true)) (by omega)
      have negcount := ones_off s un
      have no := unit_bound f ih (s := Function.update s u (some false)) (by rwa [negcount])
        edge (by simp) (negcount ▸ nv)
      have split := optimum_split f un
      change optimum f s+1≤2^(k+1+1)
      change optimum f _+1≤2^(k+1) at yes
      omega
    · have h := unit_bound f ih gap edge off nv
      have positive : 1≤2^(k+1) := Nat.one_le_two_pow
      change optimum f s+1≤2^(k+1+1)
      omega

end CoverTreeResearch
