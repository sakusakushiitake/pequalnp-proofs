import Research.MonotoneCertificate

namespace PlaneResearch.ShardFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.MonotoneCertificate (monoGate monotone_checked)

def table : Fin 10 → ℕ := ![0xaaa8a880,0xe888a888,0xe888e880,0xe8a8a880,0xe8a8c880,0xe8a8e800,0xeaa8c080,0xeaaac000,0xeac8e000,0xaaa8a888]
def bound : Fin 10 → ℕ := ![8,6,8,9,8,7,7,4,7,6]
private def plan0 : List Gate := [⟨.and,[1,2]⟩,⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[2,6]⟩,⟨.or,[1,8]⟩,⟨.and,[7,9]⟩,⟨.or,[5,10]⟩,⟨.and,[0,11]⟩]
private def plan1 : List Gate := [⟨.and,[2,3]⟩,⟨.and,[0,5]⟩,⟨.and,[4,5]⟩,⟨.or,[0,7]⟩,⟨.and,[1,8]⟩,⟨.or,[6,9]⟩]
private def plan2 : List Gate := [⟨.or,[0,1]⟩,⟨.or,[2,4]⟩,⟨.and,[3,5]⟩,⟨.and,[2,7]⟩,⟨.or,[6,7]⟩,⟨.and,[0,9]⟩,⟨.and,[1,10]⟩,⟨.or,[8,11]⟩]
private def plan3 : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[0,5]⟩,⟨.and,[1,7]⟩,⟨.and,[2,8]⟩,⟨.or,[2,8]⟩,⟨.and,[6,10]⟩,⟨.and,[0,11]⟩,⟨.or,[9,12]⟩]
private def plan4 : List Gate := [⟨.and,[0,1]⟩,⟨.and,[1,3]⟩,⟨.and,[0,4]⟩,⟨.and,[2,5]⟩,⟨.or,[2,5]⟩,⟨.or,[6,8]⟩,⟨.or,[7,10]⟩,⟨.and,[9,11]⟩]
private def plan5 : List Gate := [⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.and,[0,4]⟩,⟨.or,[2,5]⟩,⟨.or,[3,7]⟩,⟨.and,[8,9]⟩,⟨.and,[6,10]⟩]
private def plan6 : List Gate := [⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[0,4]⟩,⟨.and,[0,6]⟩,⟨.or,[5,7]⟩,⟨.or,[3,8]⟩,⟨.and,[9,10]⟩]
private def plan7 : List Gate := [⟨.and,[1,2]⟩,⟨.and,[0,4]⟩,⟨.and,[3,5]⟩,⟨.or,[6,7]⟩]
private def plan8 : List Gate := [⟨.and,[1,2]⟩,⟨.or,[1,3]⟩,⟨.and,[2,3]⟩,⟨.or,[0,5]⟩,⟨.or,[4,7]⟩,⟨.and,[8,9]⟩,⟨.and,[6,10]⟩]
private def plan9 : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.and,[4,6]⟩,⟨.or,[5,7]⟩,⟨.or,[1,8]⟩,⟨.and,[0,9]⟩]
def plan : Fin 10 → List Gate := ![plan0,plan1,plan2,plan3,plan4,plan5,plan6,plan7,plan8,plan9]
def circuit (i : Fin 10) : Circuit := ⟨plan i,4+(plan i).length⟩
def Computes (t : ℕ) (g : List Gate) (o : ℕ) := ∀ x : Fin 5 → Bool,
  Circuit.eval ⟨g,o⟩ (List.ofFn x) = Nat.testBit t (∑ j : Fin 5, if x j then 2^j.val else 0)
abbrev Mon (g : List Gate) := ∀ h ∈ g, (h.op=.and ∨ h.op=.or) ∧ h.inputs.length≤2
theorem sizes : ∀ i, (plan i).length=bound i := by decide +kernel
private theorem ops : ∀ i, (plan i).all monoGate=true := by decide +kernel
theorem monotone (i : Fin 10) : Mon (plan i) := monotone_checked (circuit i) (ops i)
private theorem truth : ∀ i (a b c d e : Bool),
    (circuit i).eval (List.ofFn (![a,b,c,d,e] : Fin 5 → Bool)) =
    Nat.testBit (table i) (∑ j : Fin 5, if (![a,b,c,d,e] : Fin 5 → Bool) j then 2^j.val else 0) := by
  decide +kernel
theorem correct (i : Fin 10) : Computes (table i) (plan i) (circuit i).output := by
  intro x
  have eta : (![x 0,x 1,x 2,x 3,x 4] : Fin 5 → Bool)=x := by funext j; fin_cases j <;> rfl
  have h := truth i (x 0) (x 1) (x 2) (x 3) (x 4)
  rw [eta] at h
  exact h

theorem large_has_replacement (i : Fin 10) (g : List Gate) (h : bound i ≤ g.length) :
    ∃ g' : List Gate, ∃ o' : ℕ, Mon g' ∧ g'.length≤g.length ∧ Computes (table i) g' o' :=
  ⟨plan i,(circuit i).output,monotone i,(sizes i) ▸ h,correct i⟩

end PlaneResearch.ShardFour
