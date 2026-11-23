import Research.StarOwners

namespace PlaneResearch.MonotoneCertificate
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

abbrev Terms (n : ℕ) := List (Finset (Fin n))
def monoGate (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length≤2)
  | _ => false
theorem monotone_checked (C : Circuit) (ok : C.gates.all monoGate=true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases op : g.op <;> simp [monoGate,op] at h ⊢ <;> assumption

def Holds {n : ℕ} (D : Terms n) (x : Fin n → Bool) : Prop :=
  ∃ S ∈ D, ∀ p ∈ S, x p=true
def impliesD {n : ℕ} (A B : Terms n) : Bool :=
  A.all (fun S => B.any (fun T => decide (T ⊆ S)))
def same {n : ℕ} (A B : Terms n) : Bool := impliesD A B && impliesD B A
def productD {n : ℕ} (A B : Terms n) : Terms n := A.flatMap (fun S => B.map (fun T => S ∪ T))

theorem entails {n : ℕ} {A B : Terms n} (ok : impliesD A B=true) {x : Fin n → Bool} :
    Holds A x → Holds B x := by
  rintro ⟨S,hS,active⟩
  obtain ⟨T,hT,sub⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok S hS)
  exact ⟨T,hT,fun p hp => active p ((of_decide_eq_true sub) hp)⟩

theorem equiv {n : ℕ} {A B : Terms n} (ok : same A B=true) (x : Fin n → Bool) :
    Holds A x ↔ Holds B x :=
  ⟨entails (Bool.and_eq_true_iff.mp ok).1,entails (Bool.and_eq_true_iff.mp ok).2⟩

private lemma holds_or {n : ℕ} (A B : Terms n) (x : Fin n → Bool) :
    Holds (A++B) x ↔ Holds A x ∨ Holds B x := by
  simp only [Holds,List.mem_append,or_and_right,exists_or]
private lemma holds_and {n : ℕ} (A B : Terms n) (x : Fin n → Bool) :
    Holds (productD A B) x ↔ Holds A x ∧ Holds B x := by
  constructor
  · rintro ⟨U,hU,active⟩
    obtain ⟨S,hs,hu⟩ := List.mem_flatMap.mp hU
    obtain ⟨T,ht,rfl⟩ := List.mem_map.mp hu
    exact ⟨⟨S,hs,fun p hp => active p (Finset.mem_union_left _ hp)⟩,
      ⟨T,ht,fun p hp => active p (Finset.mem_union_right _ hp)⟩⟩
  · rintro ⟨⟨S,hs,sa⟩,⟨T,ht,ta⟩⟩
    exact ⟨S ∪ T,List.mem_flatMap.mpr ⟨S,hs,List.mem_map.mpr ⟨T,ht,rfl⟩⟩,
      fun p hp => (Finset.mem_union.mp hp).elim (sa p) (ta p)⟩

def atWire {n : ℕ} (proof : List (Terms n)) (j : ℕ) : Terms n :=
  if h : j<n then [{⟨j,h⟩}] else proof.getD (j-n) []
def checkGate {n : ℕ} (proof : List (Terms n)) (k : ℕ) (g : Gate) : Bool :=
  match g.inputs with
  | [a,b] => decide (a<n+k ∧ b<n+k) && (match g.op with
    | .and => same (atWire proof (n+k)) (productD (atWire proof a) (atWire proof b))
    | .or => same (atWire proof (n+k)) (atWire proof a ++ atWire proof b)
    | _ => false)
  | _ => false

/-- Each wire is provided with a list of sufficient positive input sets.
Local absorption checks are enough to prove the value on all Boolean inputs. -/
theorem wire {n : ℕ} (C : Circuit) (proof : List (Terms n))
    (check : ∀ k : Fin C.gates.length, checkGate proof k.val (C.gates.get k)=true)
    (x : Fin n → Bool) (i : ℕ) (valid : i<n+C.gates.length) :
    W C i x=true ↔ Holds (atWire proof i) x := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases raw : i<n
    · let p : Fin n := ⟨i,raw⟩
      change W C p.val x=true ↔ _
      simp [atWire,raw,Holds,p]
      exact input C p x
    · let k := i-n
      have hk : k<C.gates.length := by dsimp [k]; omega
      have eq : i=n+k := by dsimp [k]; omega
      have cert := check ⟨k,hk⟩
      change checkGate proof k C.gates[k]=true at cert
      rw [eq,gate C k hk]
      cases ins : C.gates[k].inputs with
      | nil => simp [checkGate,ins] at cert
      | cons a tail =>
        cases tail with
        | nil => simp [checkGate,ins] at cert
        | cons b rest =>
          cases rest with
          | cons d ds => simp [checkGate,ins] at cert
          | nil =>
            simp only [checkGate,ins,Bool.and_eq_true_iff,decide_eq_true_eq] at cert
            obtain ⟨⟨la,lb⟩,h⟩ := cert
            have aa := ih a (by omega) (by omega)
            have bb := ih b (by omega) (by omega)
            cases op : C.gates[k].op with
            | and =>
              rw [op] at h
              simpa [GateOp.eval,la,lb,aa,bb,(equiv h x),holds_and] using
                (Iff.rfl : Holds (productD (atWire proof a) (atWire proof b)) x ↔ _)
            | or =>
              rw [op] at h
              simp [GateOp.eval,la,lb,aa,bb,(equiv h x),holds_or]
            | _ => simp [op] at h

def edgeTerms {n : ℕ} (E : List (Fin n × Fin n)) : Terms n := E.map (fun z => {z.1,z.2})
theorem edges {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) :
    Holds (edgeTerms E) x ↔ ∃ p q, (p,q) ∈ E ∧ x p=true ∧ x q=true := by
  constructor
  · rintro ⟨S,hS,active⟩
    obtain ⟨⟨p,q⟩,mem,rfl⟩ := List.mem_map.mp hS
    exact ⟨p,q,mem,active _ (by simp),active _ (by simp)⟩
  · rintro ⟨p,q,mem,hp,hq⟩
    refine ⟨{p,q},List.mem_map.mpr ⟨(p,q),mem,rfl⟩,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact hp
    · exact Finset.mem_singleton.mp h ▸ hq

end PlaneResearch.MonotoneCertificate
