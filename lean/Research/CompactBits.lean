import Research.CompactTables

namespace PlaneResearch.CompactBits
open PlaneResearch.SideTables

def consume (bits left : ℕ) : List ℕ → Option (ℕ × ℕ)
  | [] => some (bits,left)
  | p::ps => if bits.testBit p then consume bits left ps
             else if left=0 then none else consume (bits ||| 2^p) (left-1) ps

def solve (bits left : ℕ) : List (List (List ℕ)) → Bool
  | [] => true
  | row::rest => row.any (fun e => match consume bits left e with
    | none => false
    | some (newBits,newLeft) => solve newBits newLeft rest)

def branch (bits left : ℕ) (rest : List (List (List ℕ))) (e : List ℕ) : Bool :=
  match consume bits left e with
  | none => false
  | some (b,l) => solve b l rest

theorem reject_cons (bits left : ℕ) (row : List (List ℕ)) (rest : List (List (List ℕ)))
    (reject : ∀ e ∈ row, branch bits left rest e=false) : solve bits left (row::rest)=false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  obtain ⟨e,he,yes⟩ := List.any_eq_true.mp ok
  change branch bits left rest e=true at yes
  simp [reject e he] at yes

def unpaid (H : Finset ℕ) (bits : ℕ) := H.filter (fun i => bits.testBit i=false)

private lemma consume_ok (H : Finset ℕ) (e : List ℕ) (bits left : ℕ)
    (ok : (unpaid H bits).card≤left) (sub : ∀ p ∈ e, p ∈ H) :
    ∃ b l, consume bits left e=some (b,l) ∧ (unpaid H b).card≤l := by
  induction e generalizing bits left with
  | nil => exact ⟨bits,left,rfl,ok⟩
  | cons p ps ih =>
    have rest : ∀ q ∈ ps, q ∈ H := fun _ h => sub _ (List.mem_cons_of_mem _ h)
    by_cases paid : bits.testBit p=true
    · simpa [consume,paid] using ih bits left ok rest
    · have off := Bool.eq_false_iff.mpr paid
      have mem : p ∈ unpaid H bits := Finset.mem_filter.mpr ⟨sub p List.mem_cons_self,off⟩
      have erased : unpaid H (bits ||| 2^p) = (unpaid H bits).erase p := by
        ext i
        by_cases pi : p=i
        · subst i; simp [unpaid,Nat.testBit_or,Nat.testBit_two_pow]
        · simp [unpaid,Nat.testBit_or,Nat.testBit_two_pow,pi,Ne.symm pi]
      have count := Finset.card_erase_add_one mem
      have leftPos : left ≠ 0 := by omega
      have next : (unpaid H (bits ||| 2^p)).card≤left-1 := by rw [erased]; omega
      simpa [consume,off,leftPos] using ih (bits ||| 2^p) (left-1) next rest

theorem solve_of (H : Finset ℕ) (rows : List (List (List ℕ))) (bits left : ℕ)
    (ok : (unpaid H bits).card≤left)
    (works : ∀ r ∈ rows, ∃ e ∈ r, ∀ p ∈ e, p ∈ H) : solve bits left rows=true := by
  induction rows generalizing bits left with
  | nil => rfl
  | cons r rows ih =>
    obtain ⟨e,he,sub⟩ := works r List.mem_cons_self
    obtain ⟨b,l,eq,ok'⟩ := consume_ok H e bits left ok sub
    apply List.any_eq_true.mpr
    exact ⟨e,he,by simp [eq,ih b l ok' (fun _ h => works _ (List.mem_cons_of_mem _ h))]⟩

private theorem possible_witness (k : ℕ) (rows : List (List (Finset ℕ))) (used : Finset ℕ)
    (ok : possible k used rows=true) :
    ∃ H : Finset ℕ, H.card≤k ∧ used⊆H ∧ ∀ r ∈ rows, ∃ e ∈ r, e⊆H := by
  induction rows generalizing used with
  | nil => exact ⟨used,of_decide_eq_true ok,Finset.Subset.rfl,by simp⟩
  | cons r rs ih =>
    obtain ⟨e,inR,good⟩ := List.any_eq_true.mp ok
    obtain ⟨H,bound,sub,works⟩ := ih _ (Bool.and_eq_true_iff.mp good).2
    refine ⟨H,bound,Finset.Subset.trans Finset.subset_union_left sub,?_⟩
    intro row hr
    rcases List.mem_cons.mp hr with rfl|rest
    · exact ⟨e,inR,Finset.Subset.trans Finset.subset_union_right sub⟩
    · exact works _ rest

theorem certifies (k : ℕ) (rows : List (List (List ℕ))) (reject : solve 0 k rows=false) :
    possible k ∅ (rows.map (List.map List.toFinset))=false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  obtain ⟨H,bound,_,works⟩ := possible_witness k _ _ ok
  have can := solve_of H rows 0 k (by simpa [unpaid] using bound) (by
    intro r hr
    obtain ⟨s,hs,sub⟩ := works _ (List.mem_map_of_mem hr)
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
    exact ⟨e,he,fun p hp => sub (List.mem_toFinset.mpr hp)⟩)
  simp [reject] at can

end PlaneResearch.CompactBits
