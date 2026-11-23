import Research.SideTables
import Mathlib.Data.Finset.Sort

namespace PlaneResearch.TablePool

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables

/-- A wire outside the base and target lists has one of at most k sorted signatures. -/
theorem pool_lower {d k : ℕ} (R T : Finset (Table d)) (rz : 0 ∈ R) (rt : top d ∈ R)
    (dis : Disjoint R T)
    (impossible : ∀ h : Fin k → Table d, (∀ i j, i ≤ j → (h i).toNat ≤ (h j).toNat) →
      (∀ i, h i ∉ T) →
      (∀ f ∈ T, ∃ a b, (a ∈ R ∪ T ∨ ∃ i, h i = a) ∧ (b ∈ R ∪ T ∨ ∃ i, h i = b) ∧
        a ≠ f ∧ b ≠ f ∧ recipe f a b) → False)
    (gs : List Gate) (w : List (Table d)) (ok : FanInTwo ⟨gs,0⟩)
    (raw : ∀ a ∈ w, a ∈ R) (hit : T ⊆ (run gs w).toFinset) :
    T.card+k+1 ≤ gs.length := by
  classical
  obtain ⟨tail,eq,len⟩ := ext_run gs w
  let H := tail.toFinset \ (R ∪ T)
  have tailT : T ⊆ tail.toFinset := by
    intro f hf
    have t := hit hf
    rw [eq,List.mem_toFinset,List.mem_append] at t
    exact List.mem_toFinset.mpr (t.resolve_left (fun hw => Finset.disjoint_left.mp dis (raw f hw) hf))
  have hT : Disjoint H T := Finset.disjoint_left.mpr (fun a ha ht =>
    (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ ht))
  have size : H.card+T.card ≤ gs.length := by
    rw [←Finset.card_union_of_disjoint hT,←len]
    exact (Finset.card_le_card (Finset.union_subset Finset.sdiff_subset tailT)).trans (List.toFinset_card_le tail)
  by_contra! small
  have hk : H.card ≤ k := by omega
  let rel (a b : Table d) := a ≤ b
  let l := H.sort rel
  let pool (i : Fin k) := l.getD i.val (top d)
  have length : l.length = H.card := Finset.length_sort ..
  have sorted : ∀ i j : Fin k, i ≤ j → (pool i).toNat ≤ (pool j).toNat := by
    intro i j ij
    by_cases hj : j.val < l.length
    · have hi : i.val < l.length := Nat.lt_of_le_of_lt ij hj
      rw [show pool i = l[i.val] from List.getD_eq_getElem _ _ hi,
          show pool j = l[j.val] from List.getD_eq_getElem _ _ hj]
      rcases Nat.eq_or_lt_of_le ij with e|lt
      · simp [e]
      · exact (H.pairwise_sort rel).rel_getElem_of_lt hi hj lt
    · rw [show pool j = top d from List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
      have less := (pool i).isLt
      simp [top]
      omega
  have inPool (a : Table d) (ha : a ∈ H) : ∃ i, pool i=a := by
    have al : a ∈ l := (Finset.mem_sort (s := H) rel).mpr ha
    obtain ⟨j,hj,eqj⟩ := List.getElem_of_mem al
    exact ⟨⟨j,by omega⟩,(List.getD_eq_getElem _ _ hj).trans eqj⟩
  apply impossible pool sorted
  · intro i
    by_cases hi : i.val < l.length
    · rw [show pool i = l[i.val] from List.getD_eq_getElem _ _ hi]
      exact Finset.disjoint_left.mp hT ((Finset.mem_sort (s := H) rel).mp (List.getElem_mem ..))
    · rw [show pool i = top d from List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Finset.disjoint_left.mp dis rt
  · intro f hf
    have nr : f ∉ R := fun hr => Finset.disjoint_left.mp dis hr hf
    obtain ⟨a,b,ha,hb,af,bf,rec⟩ := first_recipe gs w f ok (fun e => nr (e ▸ rz))
      (fun e => nr (e ▸ rt)) (fun hw => nr (raw _ hw)) (List.mem_toFinset.mp (hit hf))
    have source (x : Table d) (hx : x ∈ run gs w ∨ x=0) : x ∈ R ∪ T ∨ ∃ i, pool i=x := by
      by_cases base : x ∈ R ∪ T
      · exact Or.inl base
      · right
        apply inPool
        apply Finset.mem_sdiff.mpr
        refine ⟨?_,base⟩
        rcases hx with wire|rfl
        · rw [eq,List.mem_append] at wire
          exact List.mem_toFinset.mpr (wire.resolve_left (fun hw => base (Finset.mem_union_left _ (raw _ hw))))
        · exact (base (Finset.mem_union_left _ rz)).elim
    exact ⟨a,b,source a ha,source b hb,af,bf,rec⟩

def admits {d : ℕ} (f : Table d) (simple l : List (Table d)) : Bool :=
  l.any (fun a => simple.contains a) || l.any (fun a => l.any (fun b => a &&& b == f))

/-- A proper OR-subset or a complement uses one helper, and an AND of two
strict supersets uses two. The numerical classification is supplied per row. -/
theorem admit_of {d : ℕ} (B : Finset (Table d)) (l simple : List (Table d)) (f : Table d)
    (realize : ∃ a b, (a ∈ B ∨ a ∈ l) ∧ (b ∈ B ∨ b ∈ l) ∧ a ≠ f ∧ b ≠ f ∧ recipe f a b)
    (classify : ∀ a b, a ≠ f → b ≠ f → recipe f a b →
      (a ∈ simple ∧ a ∉ B) ∨ (b ∈ simple ∧ b ∉ B) ∨ (a ∉ B ∧ b ∉ B ∧ a &&& b = f)) :
    admits f simple l = true := by
  obtain ⟨a,b,aa,bb,af,bf,op⟩ := realize
  rcases classify a b af bf op with ⟨ha,na⟩|⟨hb,nb⟩|⟨na,nb,eq⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨a,aa.resolve_left na,by simpa using ha⟩))
  · exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨b,bb.resolve_left nb,by simpa using hb⟩))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr
      ⟨a,aa.resolve_left na,List.any_eq_true.mpr ⟨b,bb.resolve_left nb,by simpa using eq⟩⟩))

end PlaneResearch.TablePool
