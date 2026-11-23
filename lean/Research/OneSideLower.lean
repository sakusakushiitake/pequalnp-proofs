import Research.PriorityRectangles
import Research.CleanLower

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.StarCounting PlaneResearch.BicliqueStar
open PlaneResearch.PriorityRectangles
open PlaneResearch.PriorityFamilies (prefer)

/-- For a bipartite square-free target, arbitrarily many extra pairs entirely
outside R can be accepted at AND gates, provided all singleton tests stay off. -/
theorem one_side_lower {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoSquare G) (R : Finset (Fin n)) (bip : ∀ p q, G.Adj p q → Across R p q)
    (H : SimpleGraph (Fin n)) (allowed : ∀ p q, H.Adj p q → (p ∉ R ∧ q ∉ R) ∨ G.Adj p q)
    (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean H C) (off : ∀ p : Fin n, W C o.val (single p)=false)
    (on' : ∀ u v, G.Adj u v → W C o.val (pair u v)=true) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card+K.card≤C.gates.length+1 := by
  classical
  let S := support (n:=n) C
  let A := (live C o).filter (fun w => ∃ a b, Rect C w a b ∧ Used R (S a) (S b))
  have pick (w : Node n C) : ∃ a b : Node n C, w ∈ A → Rect C w a b ∧ Used R (S a) (S b) := by
    by_cases h : w ∈ A
    · obtain ⟨a,b,r⟩ := (Finset.mem_filter.mp h).2
      exact ⟨a,b,fun _ => r⟩
    · exact ⟨o,o,fun z => (h z).elim⟩
  choose x y spec using pick
  let U := (family C o).image (prefer R)
  let X (w : Node n C) := prefer R (S (x w))
  let Y (w : Node n C) := prefer R (S (y w))
  have raw {w a b : Node n C} (r : Rect C w a b) :
      ∀ p ∈ S a, ∀ q ∈ S b, (p ∉ R ∧ q ∉ R) ∨ G.Adj p q :=
    fun p hp q hq => allowed p q (rect_cross H C ops clean r hp hq)
  have made (w) (hw : w ∈ A) : X w ∈ U ∧ Y w ∈ U := by
    have pa := rect_parents C (spec w hw).1
    have lw := (Finset.mem_filter.mp hw).1
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (live_parent C o w (x w) lw (by simp [pa]))),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (live_parent C o w (y w) lw (by simp [pa])))⟩
  have pos (w) (hw : w ∈ A) : (S (x w)).Nonempty ∧ (S (y w)).Nonempty := by
    obtain ⟨_,_,_,_,_,_,_,ne⟩ := (spec w hw).1
    exact ne
  have cover (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
      ∃ t ∈ A, ∃ a ∈ X t, ∃ b ∈ Y t, e=s(a,b) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨t,lt,a,b,r,hits⟩ := edge_rect C o ops two u v (on' u v adj) (off u) (off v)
      have excl : ∀ p ∈ S a, ∀ q ∈ S b, p ∈ R → q ∉ R := by
        intro p hp q hq pr qr
        rcases raw r p hp q hq with bad|edge
        · exact bad.1 pr
        · rcases bip p q edge with ⟨_,f⟩|⟨_,f⟩
          · exact f qr
          · exact f pr
      have put {p q} (ap : p ∈ S a) (bq : q ∈ S b) (edge : G.Adj p q) :
          ∃ h : t ∈ A, p ∈ X t ∧ q ∈ Y t := by
        obtain ⟨used,px,qy⟩ := keep_edge ap bq (bip p q edge) excl
        have ht : t ∈ A := Finset.mem_filter.mpr ⟨lt,a,b,r,used⟩
        obtain ⟨ex,ey⟩ := rect_unique C r (spec t ht).1
        exact ⟨ht,by simpa only [X,←ex] using px,by simpa only [Y,←ey] using qy⟩
      rcases hits with ⟨ha,hb⟩|⟨ha,hb⟩
      · obtain ⟨ht,hu,hv⟩ := put ha hb adj
        exact ⟨t,ht,u,hu,v,hv,rfl⟩
      · obtain ⟨ht,hv,hu⟩ := put ha hb adj.symm
        exact ⟨t,ht,v,hv,u,hu,Sym2.eq_swap⟩
  have quiet := quiet_of_clean H C clean
  have split := first_union C o ops two quiet
  obtain ⟨m,K,small,meets⟩ := rectangle_counts G sq G.edgeFinset A X Y U made
    (fun w hw => ⟨nonempty (pos w hw).1,nonempty (pos w hw).2⟩)
    (fun w hw _ hp _ hq => PriorityRectangles.cross (spec w hw).2 (raw (spec w hw).1) hp hq)
    cover (PriorityFamilies.projected_split R (family C o) (fun s hs h => (split s hs h).2))
  have sub : ((family C o).filter (fun s => 1<s.card)) ⊆ (forks C o).image (support C) := by
    intro s hs
    obtain ⟨made',big⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_image.mpr (split s made' big).1
  have b := (PriorityFamilies.big_count R (family C o)).trans ((Finset.card_le_card sub).trans Finset.card_image_le)
  change (U.filter (fun s => 1<s.card)).card ≤ (forks C o).card at b
  have root : A ⊆ zeros C o := by
    intro w hw
    obtain ⟨k,hk,eq,ga,_⟩ := (spec w hw).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,eq ▸ and_set C quiet k hk ga⟩
  have budget := gate_budget C o A ops two quiet root (by
    intro w hw p hp
    rw [rect_parents C (spec w hw).1] at hp
    rcases Finset.mem_insert.mp hp with h|h
    · exact h ▸ (pos w hw).1
    · exact Finset.mem_singleton.mp h ▸ (pos w hw).2)
  refine ⟨K,?_,by omega⟩
  intro u v uv
  obtain ⟨p,hp,h⟩ := meets s(u,v) (SimpleGraph.mem_edgeFinset.mpr uv)
  rcases Sym2.mem_iff.mp h with rfl|rfl
  · exact Or.inl hp
  · exact Or.inr hp

end PlaneResearch.CleanWireModel
