import Research.CleanLower
import Research.PlaneClean

namespace PlaneResearch.PlaneCleanBound
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.CleanWireModel
open PlaneResearch.BicliqueStar PlaneResearch.PlaneClean
abbrev V := Fin 26
private instance : DecidableRel graph.Adj := fun p q => inferInstanceAs (Decidable (adjacent p q))

private def neighbors (a b : V) : Finset V := Finset.univ.filter (fun v => adjacent a v ∧ adjacent b v)
private theorem common : ∀ a b : V, a ≠ b → (neighbors a b).card≤1 := by decide +kernel
theorem noSquare : NoSquare graph := by
  intro a b c d ab bc cd da
  by_cases eq : a=c
  · exact Or.inl eq
  · right
    apply Finset.card_le_one.mp (common a c eq)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩

private def recorded : Finset (Sym2 V) := edges.image (fun p => s(p.1,p.2))
private theorem recordedCount : recorded.card=52 := by decide +kernel
theorem edge_count_le : 52≤graph.edgeFinset.card := by
  rw [←recordedCount]
  apply Finset.card_le_card
  intro e he
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (show graph.Adj p.1 p.2 from Or.inl hp)

private def left (i : Fin 13) : V := ⟨i.val,by omega⟩
private def right (i : Fin 13) : V := ⟨13+(13-i.val)%13,by have := Nat.mod_lt (13-i.val) (by decide : 0<13); omega⟩
private def slot (v : V) : Fin 13 := ⟨(if v.val<13 then v.val else 26-v.val)%13,Nat.mod_lt _ (by decide)⟩
private theorem matching : ∀ i, graph.Adj (left i) (right i) := by decide +kernel
private theorem inverse : ∀ i, slot (left i)=i ∧ slot (right i)=i := by decide +kernel

theorem cover_lower (K : Finset V) (cover : ∀ u v, graph.Adj u v → u ∈ K ∨ v ∈ K) : 13≤K.card := by
  let pick (i : Fin 13) := if left i ∈ K then left i else right i
  have undo (i : Fin 13) : slot (pick i)=i := by
    dsimp only [pick]
    split
    · exact (inverse i).1
    · exact (inverse i).2
  have bound : (Finset.univ : Finset (Fin 13)).card≤K.card := by
    apply Finset.card_le_card_of_injOn pick
    · intro i _
      by_cases l : left i ∈ K
      · simpa [pick,l] using l
      · simpa [pick,l] using (cover _ _ (matching i)).resolve_left l
    · intro i _ j _ h
      exact (undo i).symm.trans ((congrArg slot h).trans (undo j))
  simpa using bound

theorem at_least_64 (C : Circuit) (o : Node 26 C)
    (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or) (two : ∀ g ∈ C.gates, g.inputs.length≤2)
    (clean : PairClean graph C) (off : ∀ p : V, W C o.val (single p)=false)
    (on' : ∀ u v, graph.Adj u v → W C o.val (pair u v)=true) : 64≤C.size := by
  obtain ⟨K,hK,lower⟩ := clean_lower graph noSquare C o ops two clean off on'
  have t := cover_lower K hK
  have e := edge_count_le
  change 64≤C.gates.length
  omega

end PlaneResearch.PlaneCleanBound
