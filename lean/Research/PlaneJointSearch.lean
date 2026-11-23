import Research.PlaneJointOrbit
import Research.PlaneDirtyTriple

namespace PlaneResearch.PlaneJointSearch
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners PlaneResearch.CleanProbeFamily
open PlaneResearch.RelabelWires PlaneResearch.PlaneDirtyTriple PlaneResearch.PlaneJointOrbit
open PlaneResearch.PlaneSideWitness (either_both)

def JointTest (C : Circuit) := Fires C (indicator crossTest) ∨
  (Fires C (indicator smallSide) ∧ Fires C (indicator largeSide))

theorem candidates :
    (∃ C : Circuit, Mono C ∧ C.size≤63 ∧ Correct C) ↔
    ∃ C : Circuit, Mono C ∧ C.size≤63 ∧ Correct C ∧ JointTest C := by
  constructor
  · rintro ⟨C,hm,size,hc⟩
    rcases either_both C hm hc size with mixed|⟨left,right⟩
    · obtain ⟨p,q,diff,miss,fire⟩ := mixed
      obtain ⟨σ,pres,hp,hq⟩ := mixed_map p q diff miss
      exact ⟨rename σ C,relabel_mono C hm σ,(size_eq σ C) ▸ size,relabel_correct C hc σ pres,
        Or.inl (move_fires C hm σ p q _ hp hq fire)⟩
    · obtain ⟨p,hp,q,hq,pq,x⟩ := left
      obtain ⟨r,hr,s,hs,rs,y⟩ := right
      obtain ⟨σ,pres,sp,sq,sr,ss⟩ := joint_map p q r s hp hq pq hr hs rs
      exact ⟨rename σ C,relabel_mono C hm σ,(size_eq σ C) ▸ size,relabel_correct C hc σ pres,
        Or.inr ⟨move_fires C hm σ p q _ sp sq x,move_fires C hm σ r s _ sr ss y⟩⟩
  · rintro ⟨C,hm,size,hc,_⟩
    exact ⟨C,hm,size,hc⟩

end PlaneResearch.PlaneJointSearch
