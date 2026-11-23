import Research.PriorityFamilies
import Research.ActiveRectangles

namespace PlaneResearch.PriorityRectangles
open PlaneResearch.PriorityFamilies

variable {V : Type*} [DecidableEq V]

def Across (R : Finset V) (p q : V) := (p ∈ R ∧ q ∉ R) ∨ (q ∈ R ∧ p ∉ R)

def Used (R A B : Finset V) := ¬ Disjoint A R ∨ ¬ Disjoint B R

theorem keep_edge {R A B : Finset V} {p q : V}
    (ap : p ∈ A) (bq : q ∈ B) (different : Across R p q)
    (exclude : ∀ x ∈ A, ∀ y ∈ B, x ∈ R → y ∉ R) :
    Used R A B ∧ p ∈ prefer R A ∧ q ∈ prefer R B := by
  rcases different with ⟨pr,_⟩|⟨qr,_⟩
  · have da : ¬Disjoint A R := fun h => Finset.disjoint_left.mp h ap pr
    have db : Disjoint B R := Finset.disjoint_left.mpr (fun y by' => exclude p ap y by' pr)
    exact ⟨Or.inl da,mem_prefer ap (Or.inl pr),mem_prefer bq (Or.inr db)⟩
  · have db : ¬Disjoint B R := fun h => Finset.disjoint_left.mp h bq qr
    have da : Disjoint A R := Finset.disjoint_left.mpr (fun x ax xr => exclude x ax q bq xr qr)
    exact ⟨Or.inr db,mem_prefer ap (Or.inr da),mem_prefer bq (Or.inl qr)⟩

theorem cross {R A B : Finset V} {G : SimpleGraph V} (used : Used R A B)
    (raw : ∀ x ∈ A, ∀ y ∈ B, (x ∉ R ∧ y ∉ R) ∨ G.Adj x y)
    {p q : V} (hp : p ∈ prefer R A) (hq : q ∈ prefer R B) : G.Adj p q := by
  apply (raw p (PriorityFamilies.subset _ _ hp) q (PriorityFamilies.subset _ _ hq)).resolve_left
  intro low
  rcases used with u|u
  · exact low.1 (Finset.mem_inter.mp (show p ∈ A ∩ R by simpa [prefer,u] using hp)).2
  · exact low.2 (Finset.mem_inter.mp (show q ∈ B ∩ R by simpa [prefer,u] using hq)).2

theorem nonempty {R A : Finset V} (ne : A.Nonempty) : (prefer R A).Nonempty := by
  by_cases d : Disjoint A R
  · simpa [prefer,d] using ne
  · simpa [prefer,d] using (Finset.not_disjoint_iff_nonempty_inter.mp d)

end PlaneResearch.PriorityRectangles
