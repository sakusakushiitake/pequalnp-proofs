import Research.ActiveRectangles
import Research.CleanZeroCount
import Research.StarOrient

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.StarCounting PlaneResearch.BicliqueStar

/-- The square-free graph bounding the AND responses can differ from the
graph of edges used for the output lower bound. -/
theorem ambient_lower {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) (sq : NoSquare H) (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean H C) (off : ∀ p : Fin n, W C o.val (single p)=false)
    (on' : ∀ u v, G.Adj u v → W C o.val (pair u v)=true) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card+K.card≤C.gates.length+1 := by
  classical
  let A := (live C o).filter (fun w => ∃ a b, Rect C w a b)
  have pick (w : Node n C) : ∃ a b : Node n C, w ∈ A → Rect C w a b := by
    by_cases h : w ∈ A
    · obtain ⟨a,b,r⟩ := (Finset.mem_filter.mp h).2
      exact ⟨a,b,fun _ => r⟩
    · exact ⟨o,o,fun z => (h z).elim⟩
  choose x y spec using pick
  let X (w : Node n C) := support C (x w)
  let Y (w : Node n C) := support C (y w)
  have positive (w) (h : w ∈ A) : (X w).Nonempty ∧ (Y w).Nonempty := by
    obtain ⟨_,_,_,_,_,_,_,t⟩ := spec w h
    exact t
  have made (w) (h : w ∈ A) : X w ∈ family C o ∧ Y w ∈ family C o := by
    have pa := rect_parents C (spec w h)
    have lw := (Finset.mem_filter.mp h).1
    exact ⟨Finset.mem_image_of_mem _ (live_parent C o w (x w) lw (by simp [pa])),
      Finset.mem_image_of_mem _ (live_parent C o w (y w) lw (by simp [pa]))⟩
  have cover (e : Sym2 (Fin n)) (h : e ∈ G.edgeFinset) :
      ∃ t ∈ A, ∃ a ∈ X t, ∃ b ∈ Y t, e=s(a,b) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp h
      obtain ⟨t,lt,a,b,r,hits⟩ := edge_rect C o ops two u v (on' u v adj) (off u) (off v)
      have ht : t ∈ A := Finset.mem_filter.mpr ⟨lt,a,b,r⟩
      obtain ⟨ex,ey⟩ := rect_unique C r (spec t ht)
      subst a; subst b
      rcases hits with ⟨ha,hb⟩|⟨ha,hb⟩
      · exact ⟨t,ht,u,ha,v,hb,rfl⟩
      · exact ⟨t,ht,v,ha,u,hb,Sym2.eq_swap⟩
  have quiet := quiet_of_clean H C clean
  have split := first_union C o ops two quiet
  obtain ⟨m,K,small,meets⟩ := rectangle_counts H sq G.edgeFinset A X Y (family C o)
    made positive (fun t ht _ ha _ hb => rect_cross H C ops clean (spec t ht) ha hb) cover
    (fun s hs big => (split s hs big).2)
  have sub : ((family C o).filter (fun s => 1<s.card)) ⊆ (forks C o).image (support C) := by
    intro s hs
    obtain ⟨made,big⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_image.mpr (split s made big).1
  have b := (Finset.card_le_card sub).trans Finset.card_image_le
  have root : A ⊆ zeros C o := by
    intro w hw
    obtain ⟨k,hk,eq,ga,_⟩ := spec w hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,eq ▸ and_set C quiet k hk ga⟩
  have budget := gate_budget C o A ops two quiet root (by
    intro w hw p hp
    rw [rect_parents C (spec w hw)] at hp
    rcases Finset.mem_insert.mp hp with h|h
    · exact h ▸ (positive w hw).1
    · exact Finset.mem_singleton.mp h ▸ (positive w hw).2)
  refine ⟨K,?_,by omega⟩
  intro u v uv
  obtain ⟨p,hp,h⟩ := meets s(u,v) (SimpleGraph.mem_edgeFinset.mpr uv)
  rcases Sym2.mem_iff.mp h with rfl|rfl
  · exact Or.inl hp
  · exact Or.inr hp

/-- If every AND is false on singleton and nonedge tests for a square-free
graph, its output edge set and a vertex cover together cost at most g+1. -/
theorem clean_lower {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoSquare G) (C : Circuit) (o : Node n C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean G C) (off : ∀ p : Fin n, W C o.val (single p)=false)
    (on' : ∀ u v, G.Adj u v → W C o.val (pair u v)=true) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card+K.card≤C.gates.length+1 :=
  ambient_lower G G sq C o ops two clean off on'

end PlaneResearch.CleanWireModel
