import Research.StarEdgeCount

namespace PlaneResearch.StarCounting
open PlaneResearch.BicliqueStar

/-- Count edges and cover vertices simultaneously when every edge lies in an
input rectangle whose two sides were formed from singleton supports. -/
theorem rectangle_counts {V I : Type*} [DecidableEq V] [DecidableEq I] [Nonempty V]
    (G : SimpleGraph V) (sq : NoSquare G) (E : Finset (Sym2 V)) (T : Finset I)
    (X Y : I → Finset V) (U : Finset (Finset V))
    (made : ∀ t ∈ T, X t ∈ U ∧ Y t ∈ U)
    (non : ∀ t ∈ T, (X t).Nonempty ∧ (Y t).Nonempty)
    (cross : ∀ t ∈ T, ∀ a ∈ X t, ∀ b ∈ Y t, G.Adj a b)
    (cover : ∀ e ∈ E, ∃ t ∈ T, ∃ a ∈ X t, ∃ b ∈ Y t, e=s(a,b))
    (split : ∀ s ∈ U, 1<s.card → ∃ a ∈ U, ∃ b ∈ U, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s) :
    E.card ≤ T.card+(U.filter (fun s => 1<s.card)).card ∧
    ∃ K : Finset V, K.card≤T.card ∧ ∀ e ∈ E, ∃ p ∈ K, p ∈ e := by
  classical
  have orient (t : I) : ∃ c : V, ∃ L : Finset V, t ∈ T →
      L ∈ U ∧ (∀ v ∈ L, G.Adj c v) ∧
      (∀ a ∈ X t, ∀ b ∈ Y t, ∃ p ∈ L, s(a,b)=s(c,p)) := by
    by_cases inT : t ∈ T
    · obtain ⟨x,xm⟩ := (non t inT).1
      obtain ⟨y,ym⟩ := (non t inT).2
      rcases bipartite_is_star G sq (X t) (Y t) (cross t inT) with small|small
      · refine ⟨x,Y t,fun _ => ⟨(made t inT).2,cross t inT x xm,?_⟩⟩
        intro a ha b hb
        have eq := Finset.card_le_one.mp small _ ha _ xm
        exact ⟨b,hb,by rw [eq]⟩
      · refine ⟨y,X t,fun _ => ⟨(made t inT).1,fun a ha => (cross t inT a ha y ym).symm,?_⟩⟩
        intro a ha b hb
        have eq := Finset.card_le_one.mp small _ hb _ ym
        exact ⟨a,ha,by rw [eq,Sym2.eq_swap]⟩
    · exact ⟨Classical.choice inferInstance,∅,fun ht => (inT ht).elim⟩
  choose center leaves h using orient
  have edge (e) (he : e ∈ E) : ∃ t ∈ T, ∃ p ∈ leaves t, e=s(center t,p) := by
    obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := cover e he
    exact ⟨t,ht,(h t ht).2.2 a ha b hb⟩
  refine ⟨star_edges G sq E T center leaves U (fun t ht => (h t ht).1) (fun t ht => (h t ht).2.1) edge split,
    T.image center,Finset.card_image_le,?_⟩
  intro e he
  obtain ⟨t,ht,p,_,rfl⟩ := edge e he
  exact ⟨center t,Finset.mem_image_of_mem _ ht,by simp⟩

end PlaneResearch.StarCounting
