import Mathlib
import PEqualNP.Defs

namespace ArcTrace1537

variable {X : Type} [Fintype X] [DecidableEq X]
abbrev Mask (X : Type) := Finset X

def firsts (n : ℕ) (S : ℕ → Mask X) (T : Finset (Mask X)) :=
  (Finset.range n).filter fun i => S i ∈ T ∧ ∀ j < i, S j ≠ S i

def parent (i : ℕ) (S : ℕ → Mask X) (A : Mask X) : Prop :=
  A.card ≤ 1 ∨ ∃ j < i, S j = A

def step (i : ℕ) (S : ℕ → Mask X) : Prop :=
  S i = ∅ ∨ S i = Finset.univ ∨ ∃ A B, parent i S A ∧ parent i S B ∧
    (S i = A ∪ B ∨ S i = A ∩ B)

private lemma first_mem {n i : ℕ} {S : ℕ → Mask X} {T : Finset (Mask X)} :
    i ∈ firsts n S T ↔ i < n ∧ S i ∈ T ∧ ∀ j < i, S j ≠ S i := by
  simp [firsts]

private theorem first_image (n : ℕ) (S : ℕ → Mask X) (T : Finset (Mask X))
    (outputs : ∀ L ∈ T, ∃ i < n, S i = L) : (firsts n S T).image S = T := by
  classical
  ext L
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact (first_mem.mp hi).2.1
  · intro h
    obtain ⟨k,hk,he⟩ := outputs L h
    have ex : ∃ i, S i = L := ⟨k,he⟩
    have eq := Nat.find_spec ex
    exact Finset.mem_image.mpr ⟨Nat.find ex, first_mem.mpr
      ⟨lt_of_le_of_lt (Nat.find_min' ex he) hk, eq.symm ▸ h, fun j hj hjj => Nat.find_min ex hj (hjj.trans eq)⟩,eq⟩

private theorem first_card (n : ℕ) (S : ℕ → Mask X) (T : Finset (Mask X))
    (outputs : ∀ L ∈ T, ∃ i < n, S i = L) : (firsts n S T).card = T.card := by
  conv_rhs => rw [← first_image n S T outputs]
  symm
  apply Finset.card_image_of_injOn
  intro i hi j hj h
  have a := (first_mem.mp hi).2.2
  have b := (first_mem.mp hj).2.2
  rcases lt_trichotomy i j with lt|eq|gt
  · exact (b i lt h).elim
  · exact eq
  · exact (a j gt h.symm).elim

private lemma overlap {A B L : Mask X} (h : A ⊆ B) (small : (B ∩ L).card ≤ 1) :
    (A ∩ L).card ≤ 1 :=
  (Finset.card_le_card (Finset.inter_subset_inter_right h)).trans small

private lemma union_small {A B L : Mask X} (a : (A ∩ L).card ≤ 1) (b : (B ∩ L).card ≤ 1) :
    ((A ∪ B) ∩ L).card ≤ 2 := by
  rw [Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans (by omega)

private lemma numeric (b k d : ℕ) (hb : b ≤ 13) (hk : 2*k < b)
    (hd : d ≤ k-1) (bound : b ≤ k-d + d.choose 2) : False := by
  have : k ≤ 6 := by omega
  interval_cases k <;> interval_cases d <;> norm_num [Nat.choose] at * <;> omega

def extra (n : ℕ) (S : ℕ → Mask X) (T : Finset (Mask X)) (H : Finset ℕ) :=
  Finset.range n \ (firsts n S T ∪ H)

def wide (n : ℕ) (S : ℕ → Mask X) (T : Finset (Mask X)) (H : Finset ℕ) : Finset ℕ := by
  classical
  exact (extra n S T H).filter fun j => S j ≠ Finset.univ ∧
    ∃ i ∈ firsts n S T, j < i ∧ S i ⊆ S j

noncomputable def owner (T : Finset (Mask X)) (A : Mask X) : Mask X := by
  classical
  exact if h : ∃ L ∈ T, A ⊆ L then h.choose else ∅

private lemma owner_eq {T : Finset (Mask X)} {A L : Mask X}
    (linear : ∀ L ∈ T, ∀ U ∈ T, L ≠ U → (L ∩ U).card ≤ 1)
    (hL : L ∈ T) (a : A ⊆ L) (size : 2 ≤ A.card) : owner T A = L := by
  classical
  have existsL : ∃ U ∈ T, A ⊆ U := ⟨L,hL,a⟩
  rw [owner, dif_pos existsL]
  by_contra ne
  obtain ⟨mem,sub⟩ := existsL.choose_spec
  have bound := (Finset.card_le_card (Finset.subset_inter sub a)).trans
    (linear _ mem L hL ne)
  omega

private theorem earlier {n i k : ℕ} {S : ℕ → Mask X} {T : Finset (Mask X)} {H : Finset ℕ}
    (linear : ∀ L ∈ T, ∀ U ∈ T, L ≠ U → (L ∩ U).card ≤ 1)
    (thin : ∀ j ∈ H, ∀ L ∈ T, (S j ∩ L).card ≤ 1)
    (fi : i ∈ firsts n S T) (ki : k ≤ i) {A : Mask X} (src : parent k S A)
    (big : 2 ≤ (A ∩ S i).card) :
    ∃ j ∈ extra n S T H, j < k ∧ S j = A := by
  obtain ⟨hin,lit,prior⟩ := first_mem.mp fi
  rcases src with raw | ⟨j,jk,rfl⟩
  · have h := Finset.card_le_card (Finset.inter_subset_left (s₁:=A) (s₂:=S i))
    omega
  · have ji := lt_of_lt_of_le jk ki
    refine ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (ji.trans hin),?_⟩,jk,rfl⟩
    intro f
    rcases Finset.mem_union.mp f with a|b
    · have h := linear _ (first_mem.mp a).2.1 _ lit (prior _ ji)
      omega
    · have h := thin _ b _ lit
      omega

private theorem wide_bound {n : ℕ} {S : ℕ → Mask X} {T : Finset (Mask X)} {H : Finset ℕ}
    (linear : ∀ L ∈ T, ∀ U ∈ T, L ≠ U → (L ∩ U).card ≤ 1)
    (size : ∀ L ∈ T, L.card = 4)
    (thin : ∀ j ∈ H, ∀ L ∈ T, (S j ∩ L).card ≤ 1)
    (run : ∀ k<n, step k S) :
    (wide n S T H).card ≤ (extra n S T H).card - 1 := by
  classical
  let K := extra n S T H
  let D := wide n S T H
  have sub : D ⊆ K := Finset.filter_subset _ _
  by_cases existsK : K.Nonempty
  · let m := K.min' existsK
    have mk : m ∈ K := Finset.min'_mem _ _
    have small (i : ℕ) (fi : i ∈ firsts n S T) (mi : m < i) (A : Mask X)
        (src : parent m S A) : (A ∩ S i).card ≤ 1 := by
      by_contra! big
      obtain ⟨j,hj,jm,_⟩ := earlier linear thin fi mi.le src (by omega)
      exact (not_lt_of_ge (K.min'_le _ hj)) jm
    have no : m ∉ D := by
      intro hd
      obtain ⟨_,ne,i,fi,mi,inc⟩ := Finset.mem_filter.mp hd
      have four := size _ (first_mem.mp fi).2.1
      have mn := (first_mem.mp fi).1
      have covered : (S m ∩ S i).card = 4 := by rwa [Finset.inter_eq_right.mpr inc]
      rcases run m (mi.trans mn) with empty|full|⟨A,B,pa,pb,join|meet⟩
      · simp [empty] at covered
      · exact ne full
      · have h := union_small (small i fi mi A pa) (small i fi mi B pb)
        rw [← join] at h
        omega
      · have h := overlap (Finset.inter_subset_left (s₁:=A) (s₂:=B)) (small i fi mi A pa)
        rw [← meet] at h
        omega
    have strict : D ⊂ K := Finset.ssubset_iff_of_subset sub |>.mpr ⟨m,mk,no⟩
    have lt := Finset.card_lt_card strict
    change D.card ≤ K.card - 1
    omega
  · have empty := Finset.not_nonempty_iff_eq_empty.mp existsK
    have dc := Finset.card_le_card sub
    change D.card ≤ K.card-1
    simpa [empty] using dc

private theorem cover {n : ℕ} {S : ℕ → Mask X} {T : Finset (Mask X)} {H : Finset ℕ}
    (linear : ∀ L ∈ T, ∀ U ∈ T, L ≠ U → (L ∩ U).card ≤ 1)
    (size : ∀ L ∈ T, L.card = 4) (proper : ∀ L ∈ T, L ≠ Finset.univ)
    (thin : ∀ j ∈ H, ∀ L ∈ T, (S j ∩ L).card ≤ 1)
    (run : ∀ k<n, step k S) (outputs : ∀ L ∈ T, ∃ i < n, S i = L) :
    T ⊆ ((extra n S T H \ wide n S T H).image fun j => owner T (S j)) ∪
      (((wide n S T H).powersetCard 2).image fun p => p.inf S) := by
  classical
  intro L hL
  obtain ⟨i,fi,rfl⟩ := Finset.mem_image.mp (show L ∈ (firsts n S T).image S by
    rwa [first_image n S T outputs])
  obtain ⟨hin,_,prior⟩ := first_mem.mp fi
  have four := size _ hL
  have priv (A : Mask X) (pa : parent i S A) (sub : A ⊆ S i) (big : 2 ≤ A.card) :
      S i ∈ (extra n S T H \ wide n S T H).image (fun j => owner T (S j)) := by
    obtain ⟨j,jk,ji,rfl⟩ := earlier linear thin fi (le_refl i) pa (by rwa [Finset.inter_eq_left.mpr sub])
    apply Finset.mem_image.mpr
    refine ⟨j,Finset.mem_sdiff.mpr ⟨jk,?_⟩,owner_eq linear hL sub big⟩
    intro hd
    obtain ⟨_,_,t,ft,_,inc⟩ := Finset.mem_filter.mp hd
    have same := size _ (first_mem.mp ft).2.1
    have ge := Finset.card_le_card inc
    exact prior _ ji (Finset.eq_of_subset_of_card_le sub (by omega))
  rcases run i hin with emp|allv|⟨A,B,pa,pb,un|it⟩
  · simp [emp] at four
  · exact (proper _ hL allv).elim
  · apply Finset.mem_union_left
    have count := Finset.card_union_le A B
    rw [← un] at count
    by_cases a : 2 ≤ A.card
    · exact priv A pa (un ▸ Finset.subset_union_left) a
    · exact priv B pb (un ▸ Finset.subset_union_right) (by omega)
  · apply Finset.mem_union_right
    have ia : S i ⊆ A := it ▸ Finset.inter_subset_left
    have ib : S i ⊆ B := it ▸ Finset.inter_subset_right
    obtain ⟨j,jk,ji,rfl⟩ := earlier linear thin fi (le_refl i) pa (by rw [Finset.inter_eq_right.mpr ia,four]; decide)
    obtain ⟨k,kk,ki,rfl⟩ := earlier linear thin fi (le_refl i) pb (by rw [Finset.inter_eq_right.mpr ib,four]; decide)
    have jd : j ∈ wide n S T H := Finset.mem_filter.mpr ⟨jk,fun he => prior _ ki (by simpa [he] using it.symm),i,fi,ji,ia⟩
    have kd : k ∈ wide n S T H := Finset.mem_filter.mpr ⟨kk,fun he => prior _ ji (by simpa [he] using it.symm),i,fi,ki,ib⟩
    have diff : j ≠ k := by
      rintro rfl
      exact prior _ ji (by simpa using it.symm)
    apply Finset.mem_image.mpr
    exact ⟨{j,k},Finset.mem_powersetCard.mpr ⟨Finset.insert_subset jd (Finset.singleton_subset_iff.mpr kd),by simp [diff]⟩,by simpa using it.symm⟩

theorem count {n : ℕ} {S : ℕ → Mask X} {T : Finset (Mask X)} {H : Finset ℕ}
    (linear : ∀ L ∈ T, ∀ U ∈ T, L ≠ U → (L ∩ U).card ≤ 1)
    (size : ∀ L ∈ T, L.card = 4) (proper : ∀ L ∈ T, L ≠ Finset.univ)
    (bound : T.card ≤ 13) (scope : H ⊆ Finset.range n)
    (thin : ∀ j ∈ H, ∀ L ∈ T, (S j ∩ L).card ≤ 1)
    (run : ∀ k<n, step k S) (outputs : ∀ L ∈ T, ∃ i < n, S i = L) :
    3*T.card+2*H.card ≤ 2*n := by
  classical
  let F := firsts n S T
  let K := extra n S T H
  let D := wide n S T H
  have fd : Disjoint F H := by
    apply Finset.disjoint_left.mpr
    intro i fi hi
    have l := (first_mem.mp fi).2.1
    have small := thin i hi _ l
    simp [size _ l] at small
  have u : F ∪ H ⊆ Finset.range n := Finset.union_subset (Finset.filter_subset _ _) scope
  have ksize : K.card = n-(T.card+H.card) := by
    change ((Finset.range n) \ (F ∪ H)).card = _
    rw [Finset.card_sdiff_of_subset u, Finset.card_range, Finset.card_union_of_disjoint fd, first_card _ _ _ outputs]
  have ub := Finset.card_le_card u
  rw [Finset.card_union_of_disjoint fd, Finset.card_range, first_card _ _ _ outputs] at ub
  have dsub : D ⊆ K := Finset.filter_subset _ _
  have wb := wide_bound linear size thin run
  change D.card ≤ K.card-1 at wb
  have c := Finset.card_le_card (cover linear size proper thin run outputs)
  refine le_of_not_gt (fun bad => numeric T.card K.card D.card bound (by omega) wb ?_)
  apply c.trans
  apply (Finset.card_union_le _ _).trans
  apply (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans
  change (K \ D).card + (D.powersetCard 2).card ≤ _
  rw [Finset.card_sdiff_of_subset dsub, Finset.card_powersetCard]

end ArcTrace1537

namespace ArcTrace1537
open PEqualNP.CircuitLowerBounds

abbrev M (n : ℕ) := Finset (Fin n)

def inputMasks (n : ℕ) : List (M n) := List.ofFn fun p : Fin n => {p}

def gateMask {n : ℕ} (W : List (M n)) (g : Gate) : M n :=
  Finset.univ.filter fun p => g.op.eval (g.inputs.map fun i => decide (p ∈ W.getD i ∅))

def appendGate {n : ℕ} (W : List (M n)) (g : Gate) := W ++ [gateMask W g]

def trace (n : ℕ) (gs : List Gate) := gs.foldl appendGate (inputMasks n)

def gatesAt (n : ℕ) (gs : List Gate) (k : ℕ) := (trace n gs).getD (n+k) ∅

private lemma trace_length (n : ℕ) (gs : List Gate) : (trace n gs).length = n+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [trace,inputMasks]
  | append_singleton gs g ih =>
    simp only [trace,List.foldl_append,List.foldl_cons,List.foldl_nil,appendGate,List.length_append,List.length_singleton] at *
    omega

private lemma get_mask {n : ℕ} (W : List (M n)) (p : Fin n) (i : ℕ) :
    (W.map (fun A => decide (p∈A))).getD i false = decide (p ∈ W.getD i ∅) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases W[i]? <;> simp

private theorem simulate {n : ℕ} (W : List (M n)) (gs : List Gate) (p : Fin n) :
    ((gs.foldl appendGate W).map (fun A => decide (p∈A))) =
    (Circuit.wires ⟨gs,0⟩ (W.map (fun A => decide (p∈A)))) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,Circuit.wires,List.foldl_cons] at *
    rw [ih]
    congr 1
    simp [appendGate,gateMask]
    congr 1
    apply List.map_congr_left
    intro i _
    cases W[i]? <;> rfl

theorem sem {n : ℕ} (gs : List Gate) (p : Fin n) (i : ℕ) :
    decide (p ∈ (trace n gs).getD i ∅) =
      (Circuit.wires ⟨gs,0⟩ (List.ofFn (fun k : Fin n => decide (k=p)))).getD i false := by
  rw [← get_mask,trace, simulate]
  simp [inputMasks,List.map_ofFn,Function.comp_def,eq_comm]

private lemma parent_transfer {X : Type} [DecidableEq X] {S R : ℕ → Mask X} {k : ℕ}
    (same : ∀ j < k, S j = R j) (A : Mask X) : parent k S A → parent k R A := by
  rintro (h|⟨j,jk,eq⟩)
  · exact Or.inl h
  · exact Or.inr ⟨j,jk,(same j jk).symm.trans eq⟩

private lemma step_transfer {X : Type} [DecidableEq X] [Fintype X] {S R : ℕ → Mask X} {k : ℕ}
    (same : ∀ j ≤ k, S j = R j) (h : step k S) : step k R := by
  rcases h with a|b|⟨A,B,pa,pb,c⟩
  · exact Or.inl ((same k (by omega)).symm.trans a)
  · exact Or.inr (Or.inl ((same k (by omega)).symm.trans b))
  · exact Or.inr (Or.inr ⟨A,B,parent_transfer (fun j hj => same j hj.le) _ pa,
      parent_transfer (fun j hj => same j hj.le) _ pb,(same k (by omega)) ▸ c⟩)

private lemma raw_mask {n : ℕ} (gs : List Gate) (p : Fin n) : (trace n gs).getD p.val ∅ = {p} := by
  induction gs using List.reverseRecOn with
  | nil => simp [trace,inputMasks,List.getD,List.getElem?_eq_getElem,p.isLt]
  | append_singleton gs g ih =>
    change ((gs ++ [g]).foldl appendGate (inputMasks n)).getD p.val ∅ = _
    rw [List.foldl_append]
    change ((trace n gs) ++ [_]).getD p.val ∅ = _
    rwa [List.getD_append _ _ _ _ (by rw [trace_length]; omega)]

private lemma read_parent {n : ℕ} (gs : List Gate) (a : ℕ) :
    parent gs.length (gatesAt n gs) ((trace n gs).getD a ∅) := by
  by_cases input : a < n
  · left
    rw [raw_mask gs (⟨a,input⟩ : Fin n)]
    simp
  · by_cases existsWire : a < n+gs.length
    · right
      refine ⟨a-n,by omega,?_⟩
      simp [gatesAt,show n+(a-n)=a by omega]
    · left
      rw [List.getD_eq_default _ _ (by rw [trace_length]; omega)]
      simp

private lemma gate_step {n : ℕ} (W : List (M n)) (g : Gate)
    (legal : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    gateMask W g = ∅ ∨ gateMask W g = Finset.univ ∨
    ∃ i j : ℕ, gateMask W g = W.getD i ∅ ∪ W.getD j ∅ ∨ gateMask W g = W.getD i ∅ ∩ W.getD j ∅ := by
  obtain ⟨op,ins⟩ := g
  rcases legal with ⟨hop,arity⟩
  change op=.and ∨ op=.or at hop
  change ins.length ≤ 2 at arity
  cases ins with
  | nil =>
    rcases hop with rfl|rfl <;> simp [gateMask,GateOp.eval]
  | cons a ins =>
    cases ins with
    | nil =>
      right; right; refine ⟨a,a, Or.inl ?_⟩
      ext p
      rcases hop with rfl|rfl <;> simp [gateMask,GateOp.eval]
    | cons b ins =>
      cases ins with
      | nil =>
        right; right; refine ⟨a,b,?_⟩
        rcases hop with rfl|rfl
        · right; ext p; simp [gateMask,GateOp.eval]
        · left; ext p; simp [gateMask,GateOp.eval]
      | cons c ins => simp at arity

theorem circuit_steps (n : ℕ) (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    ∀ k < gs.length, step k (gatesAt n gs) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    intro k hk
    have add : trace n (gs++[g]) = trace n gs ++ [gateMask (trace n gs) g] := by simp [trace,appendGate,List.foldl_append]
    have same (j : ℕ) (hj : j < gs.length) : gatesAt n gs j = gatesAt n (gs++[g]) j := by
      simp only [gatesAt,add]
      rw [List.getD_append _ _ _ _ (by rw [trace_length]; omega)]
    by_cases old : k < gs.length
    · exact step_transfer (fun j hj => same j (by omega)) (ih (fun a ha => legal a (by simp [ha])) k old)
    · have eq : k = gs.length := by simp at hk; omega
      subst k
      have here : gatesAt n (gs++[g]) gs.length = gateMask (trace n gs) g := by
        simp [gatesAt,add,← trace_length n gs,List.getD]
      have source (i : ℕ) := parent_transfer same _ (read_parent (n:=n) gs i)
      rcases gate_step (trace n gs) g (legal g (by simp)) with e|f|⟨a,b,h⟩
      · exact Or.inl (here.trans e)
      · exact Or.inr (Or.inl (here.trans f))
      · exact Or.inr (Or.inr ⟨_,_,source a,source b,here.symm ▸ h⟩)

end ArcTrace1537

namespace ArcTrace1537

theorem orderThree : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin N → ℕ), N = (3 : ℕ) * (3 : ℕ) + (3 : ℕ) + 1 → (∀ l0 : Fin N, (Finset.univ.filter (fun p0 : Fin N => I p0 l0)).card = (3 : ℕ) + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ ak : ℕ, ak < gates.length → (Finset.univ.filter (fun au : Fin N => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun auk : Fin N => decide (auk = au)))).getD (N + ak) false = true)).card ≤ 1 → ∀ ax : Fin N → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn ax)).getD (N + ak) false = decide (∃ av : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun avk : Fin N => decide (avk = av)))).getD (N + ak) false = true ∧ ax av = true)) → (∀ (l2 : Fin N) (x : Fin N → Bool), (∀ cl : Fin N, (Finset.univ.filter (fun cp : Fin N => I cp cl ∧ x cp = true)).card ≤ 2) → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out l2) false = decide (∃ p3 : Fin N, I p3 l2 ∧ x p3 = true)) → ∀ (B : Finset (Fin N)) (H : Finset (Fin gates.length)), (∀ l3 ∈ B, ¬ (∃ ey : Fin N → Bool, (∀ eal : Fin N, (Finset.univ.filter (fun eap : Fin N => I eap eal ∧ ey eap = true)).card ≤ 2) ∧ (∀ ep0 : Fin N, I ep0 l3 → ey ep0 = false) ∧ ∀ ebw : ℕ, (∃ (ebk : ℕ) (ebg : PEqualNP.CircuitLowerBounds.Gate), (∀ ebK : Set ℕ, (∀ ebk0 : ℕ, ebk0 < gates.length → out l3 = N + ebk0 → (∀ ebu0 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun ebu0k : Fin N => decide (ebu0k = ebu0)))).getD (N + ebk0) false = true → ebu0 ∈ (Finset.univ.filter (fun es : Fin N => I es l3))) → ebk0 ∈ ebK) → (∀ ebk1 ∈ ebK, ∀ (ebg1 : PEqualNP.CircuitLowerBounds.Gate) (ebk2 : ℕ), gates[ebk1]? = some ebg1 → N + ebk2 ∈ ebg1.inputs → ebk2 < ebk1 → (∀ ebu1 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun ebu1k : Fin N => decide (ebu1k = ebu1)))).getD (N + ebk2) false = true → ebu1 ∈ (Finset.univ.filter (fun es : Fin N => I es l3))) → ebk2 ∈ ebK) → ebk ∈ ebK) ∧ gates[ebk]? = some ebg ∧ ebg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ebw ∈ ebg.inputs ∧ ebw < N + ebk ∧ ¬ (∀ ebu2 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun ebu2k : Fin N => decide (ebu2k = ebu2)))).getD (ebw) false = true → ebu2 ∈ (Finset.univ.filter (fun es : Fin N => I es l3)))) → ∃ eu4 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun eu4k : Fin N => decide (eu4k = eu4)))).getD (ebw) false = true ∧ ey eu4 = true)) → (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin N => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin N => decide (u5k = u5)))).getD (N + k5.val) false = true)).card ∧ ∃ l4 : Fin N, (∃ fy : Fin N → Bool, (∀ fal : Fin N, (Finset.univ.filter (fun fap : Fin N => I fap fal ∧ fy fap = true)).card ≤ 2) ∧ (∀ fp0 : Fin N, I fp0 l4 → fy fp0 = false) ∧ ∀ fbw : ℕ, (∃ (fbk : ℕ) (fbg : PEqualNP.CircuitLowerBounds.Gate), (∀ fbK : Set ℕ, (∀ fbk0 : ℕ, fbk0 < gates.length → out l4 = N + fbk0 → (∀ fbu0 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun fbu0k : Fin N => decide (fbu0k = fbu0)))).getD (N + fbk0) false = true → fbu0 ∈ (Finset.univ.filter (fun fs : Fin N => I fs l4))) → fbk0 ∈ fbK) → (∀ fbk1 ∈ fbK, ∀ (fbg1 : PEqualNP.CircuitLowerBounds.Gate) (fbk2 : ℕ), gates[fbk1]? = some fbg1 → N + fbk2 ∈ fbg1.inputs → fbk2 < fbk1 → (∀ fbu1 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun fbu1k : Fin N => decide (fbu1k = fbu1)))).getD (N + fbk2) false = true → fbu1 ∈ (Finset.univ.filter (fun fs : Fin N => I fs l4))) → fbk2 ∈ fbK) → fbk ∈ fbK) ∧ gates[fbk]? = some fbg ∧ fbg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ fbw ∈ fbg.inputs ∧ fbw < N + fbk ∧ ¬ (∀ fbu2 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun fbu2k : Fin N => decide (fbu2k = fbu2)))).getD (fbw) false = true → fbu2 ∈ (Finset.univ.filter (fun fs : Fin N => I fs l4)))) → ∃ fu4 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun fu4k : Fin N => decide (fu4k = fu4)))).getD (fbw) false = true ∧ fy fu4 = true) ∧ ∀ u6 : Fin N, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin N => decide (u6k = u6)))).getD (N + k5.val) false = true → I u6 l4) → (3 : ℕ) * B.card + 2 * H.card ≤ 2 * gates.length := by

  classical
  intro N I inst gs out plane width incidence legal normalized correct B H bad charged
  have cardN : N = 13 := by omega
  let line (l : Fin N) : M N := Finset.univ.filter (fun p => I p l)
  have size (l : Fin N) : (line l).card = 4 := width l
  have sep (l u : Fin N) (ne : l ≠ u) : (line l ∩ line u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra diff
    obtain ⟨t,_,uniq⟩ := incidence p q diff
    have h1 : I p l ∧ I p u := by simpa [line] using hp
    have h2 : I q l ∧ I q u := by simpa [line] using hq
    exact ne ((uniq l ⟨h1.1,h2.1⟩).trans (uniq u ⟨h1.2,h2.2⟩).symm)
  have inject : Function.Injective line := by
    intro l u eq
    by_contra ne
    have h := sep l u ne
    rw [eq,Finset.inter_self,size] at h
    omega
  have target (l : Fin N) : (trace N gs).getD (out l) ∅ = line l := by
    ext p
    have admissible (u : Fin N) :
        (Finset.univ.filter (fun z : Fin N => I z u ∧ decide (z=p)=true)).card ≤ 2 := by
      have sub : (Finset.univ.filter (fun z : Fin N => I z u ∧ decide (z=p)=true)) ⊆ {p} := by
        intro z hz
        simpa using (Finset.mem_filter.mp hz).2.2
      have h := Finset.card_le_card sub
      simp only [Finset.card_singleton] at h
      omega
    have corr := correct l (fun z : Fin N => decide (z=p)) admissible
    have yes := (sem gs p (out l)).trans corr
    simpa [line] using (decide_eq_decide.mp yes)
  let T := B.image line
  let U := H.image Fin.val
  have bc : T.card=B.card := Finset.card_image_of_injective _ inject
  have hc : U.card=H.card := Finset.card_image_of_injective _ Fin.val_injective
  have thin : ∀ j ∈ U, ∀ L ∈ T, (gatesAt N gs j ∩ L).card ≤ 1 := by
    intro j hj L hL
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨_,u,ok,inc⟩ := charged t ht
    have ne : u ≠ l := by intro e; exact bad l hl (e ▸ ok)
    apply overlap (B:=line u) _ (sep u l ne)
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,inc p ?_⟩
    rw [← sem]
    exact decide_eq_true hp
  have outputs : ∀ L ∈ T, ∃ i < gs.length, gatesAt N gs i=L := by
    intro L hl
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hl
    have eq := target l
    have four := size l
    by_cases input : out l < N
    · rw [raw_mask gs (⟨out l,input⟩ : Fin N)] at eq
      rw [← eq] at four
      simp at four
    · by_cases range : out l < N+gs.length
      · exact ⟨out l-N,by omega,by simpa [gatesAt,show N+(out l-N)=out l by omega] using eq⟩
      · rw [List.getD_eq_default _ _ (by rw [trace_length]; omega)] at eq
        rw [← eq] at four
        simp at four
  have bound := count (n:=gs.length) (S:=gatesAt N gs) (T:=T) (H:=U)
    (by
      intro L hL A hA ne
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hL
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hA
      exact sep l u (fun e => ne (congrArg line e)))
    (by intro L h; obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp h; exact size l)
    (by
      intro L h e
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp h
      have four := size l
      rw [e] at four
      simp at four
      omega)
    (by have h := Finset.card_le_univ B; simp at h; omega)
    (by intro j h; obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp h; exact Finset.mem_range.mpr k.isLt)
    thin (circuit_steps N gs legal) outputs
  omega

end ArcTrace1537
