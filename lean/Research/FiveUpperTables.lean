import Research.SideTables
import Research.MonotoneCertificate

namespace PlaneResearch.FiveUpperTables
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneResearch.SideTables (run wire_bits)
open PlaneResearch.MonotoneCertificate (monoGate monotone_checked)

def inputs : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def code (x : Fin 5 → Bool) : ℕ := ∑ i : Fin 5, if x i then 2^i.val else 0

private lemma encoded : ∀ (a b c d e : Bool),
    let x : Fin 5 → Bool := ![a,b,c,d,e]
    code x<32 ∧ inputs.map (fun v => v.getLsbD (code x))=List.ofFn x := by
  decide +kernel

lemma sample (x : Fin 5 → Bool) : code x<32 ∧ inputs.map (fun v => v.getLsbD (code x))=List.ofFn x := by
  have h := encoded (x 0) (x 1) (x 2) (x 3) (x 4)
  have eq : (![x 0,x 1,x 2,x 3,x 4] : Fin 5 → Bool)=x := by funext i; fin_cases i <;> rfl
  exact eq ▸ h

abbrev Row := ℕ × ℕ × List Gate
def circuit (r : Row) : Circuit := ⟨r.2.2,4+r.2.2.length⟩
def checked (r : Row) : Bool :=
  let C := circuit r
  decide (C.size=r.2.1) && C.gates.all monoGate &&
    decide ((run C.gates inputs).getD C.output 0=BitVec.ofNat 32 r.1)

theorem checked_sound (r : Row) (h : checked r=true) :
    (circuit r).size=r.2.1 ∧ Monotone2 (circuit r) ∧
      ∀ x : Fin 5 → Bool, (circuit r).eval (List.ofFn x)=r.1.testBit (code x) := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hs,hm⟩ := Bool.and_eq_true_iff.mp ha
  have mon := monotone_checked (circuit r) hm
  refine ⟨of_decide_eq_true hs,mon,?_⟩
  intro x
  obtain ⟨lt,eq⟩ := sample x
  have bits := wire_bits (circuit r).gates inputs ⟨code x,lt⟩ (circuit r).output
    (fun g hg => ⟨(mon g hg).1.imp_right Or.inl,(mon g hg).2⟩)
  change ((run (circuit r).gates inputs).getD (circuit r).output 0).getLsbD (code x) =
    (circuit r).eval (inputs.map (fun v => v.getLsbD (code x))) at bits
  rw [eq,of_decide_eq_true hb] at bits
  rw [BitVec.getLsbD_ofNat] at bits
  simpa only [lt,decide_true,Bool.true_and] using bits.symm

def a (i j : ℕ) : Gate := ⟨.and,[i,j]⟩
def o (i j : ℕ) : Gate := ⟨.or,[i,j]⟩

end PlaneResearch.FiveUpperTables
