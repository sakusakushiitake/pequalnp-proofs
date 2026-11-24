import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace Incidence1393
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def references {j : ℕ} (C : Circuit) (fa fb : Fin j → ℕ) :=
  C.gates.flatMap Gate.inputs ++ List.ofFn fa ++ List.ofFn fb

private lemma gates_len (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    have ah := arity a List.mem_cons_self
    have rest := ih (fun g hg => arity g (List.mem_cons_of_mem _ hg))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    omega

theorem reference_count {j : ℕ} (C : Circuit) (fa fb : Fin j → ℕ) (mono : Monotone2 C) :
    (references C fa fb).length ≤ 2*(C.size+j) := by
  have b := gates_len C.gates (fun g hg => (mono g hg).2)
  simp only [references,List.length_append,List.length_ofFn,Circuit.size]
  omega

private def runGates (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma on_wires (gs : List Gate) (R : List ℕ) (w v : List Bool) (len : w.length=v.length)
    (same : ∀ i ∈ R, w.getD i false = v.getD i false)
    (reads : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∈ R) :
    ∀ i ∈ R, (runGates gs w).getD i false = (runGates gs v).getD i false := by
  induction gs generalizing w v with
  | nil => exact same
  | cons a gs ih =>
    have eq : (a.inputs.map fun i => w.getD i false) = (a.inputs.map fun i => v.getD i false) := by
      exact List.map_congr_left (fun i hi => same i (reads a List.mem_cons_self i hi))
    change ∀ i ∈ R, (runGates gs (w ++ [a.op.eval _])).getD i false = (runGates gs (v ++ [a.op.eval _])).getD i false
    rw [eq]
    apply ih
    · simp [len]
    · intro i hi
      by_cases a : i < w.length
      · rw [List.getD_append _ _ _ _ a, List.getD_append _ _ _ _ (len ▸ a)]
        exact same i hi
      · by_cases b : i=w.length
        · subst i
          simp [List.getD, len]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro g hg i hi
      exact reads g (List.mem_cons_of_mem _ hg) i hi

theorem factor_agree {n j : ℕ} (C : Circuit) (fa fb : Fin j → ℕ) (x y : Fin n → Bool)
    (same : ∀ i : Fin n, i.val ∈ references C fa fb → x i=y i) :
    ∀ a ∈ references C fa fb, (C.wires (List.ofFn x)).getD a false = (C.wires (List.ofFn y)).getD a false := by
  apply on_wires C.gates _ _ _ (by simp)
  · intro i hi
    by_cases h : i<n
    · simpa [List.getD,List.getElem?_eq_getElem,h] using same ⟨i,h⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro g hg i hi
    simp only [references,List.mem_append,List.mem_flatMap]
    exact Or.inl (Or.inl ⟨g,hg,hi⟩)

def pt (N : ℕ) (R : List ℕ) := Finset.univ.filter (fun i : Fin N => i.val ∈ R)
def ln (N : ℕ) (R : List ℕ) := Finset.univ.filter (fun i : Fin N => N+i.val ∈ R)

theorem both_size (N : ℕ) (R : List ℕ) : (pt N R).card+(ln N R).card ≤ R.length := by
  let a : Fin N ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  let b : Fin N ↪ ℕ := ⟨fun i => N+i.val, fun i j eq => Fin.ext (Nat.add_left_cancel eq)⟩
  have disj : Disjoint ((pt N R).map a) ((ln N R).map b) := by
    apply Finset.disjoint_left.mpr
    rintro _ hp hl
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨l,_,eq⟩ := Finset.mem_map.mp hl
    change N+l.val=p.val at eq
    omega
  have sub : (pt N R).map a ∪ (ln N R).map b ⊆ R.toFinset := by
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hl
    · obtain ⟨p,hh,rfl⟩ := Finset.mem_map.mp hp
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hh).2
    · obtain ⟨l,hh,rfl⟩ := Finset.mem_map.mp hl
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hh).2
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le R)
  simpa only [Finset.card_union_of_disjoint disj, Finset.card_map] using bound

def pairBits {N : ℕ} (p l : Fin N) (v : Fin (N+N)) : Bool :=
  if v=Fin.castAdd N p then true else if v=Fin.natAdd N l then true else false

def pointBits {N : ℕ} (p : Fin N) (v : Fin (N+N)) : Bool := decide (v=Fin.castAdd N p)
def lineBits {N : ℕ} (l : Fin N) (v : Fin (N+N)) : Bool := decide (v=Fin.natAdd N l)


open PEqualNP.MetaComplexity.Helpers

def roots {J : ℕ} (fa fb : Fin J → ℕ) : Finset ℕ :=
  Finset.univ.image fa ∪ Finset.univ.image fb

noncomputable def coneList {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List ℕ :=
  ((roots fa fb).biUnion fun r => (suppsFrom C.gates (inputSupps (N+N))).getD r ∅).toList.map Fin.val

lemma rootCount {J : ℕ} (fa fb : Fin J → ℕ) : (roots fa fb).card ≤ 2*J := by
  apply (Finset.card_union_le _ _).trans
  have h1 := (Finset.card_image_le (s:=Finset.univ) (f:=fa))
  have h2 := (Finset.card_image_le (s:=Finset.univ) (f:=fb))
  simp only [Finset.card_univ,Fintype.card_fin] at h1 h2
  omega

lemma coneCount {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (mono : Monotone2 C) :
    (coneList N C fa fb).length ≤ C.size + (roots fa fb).card := by
  have h := cnt_suppsFrom C.gates 0 (inputSupps (N+N)) (fun g hg => ⟨by
    rcases (mono g hg).1 with a|o
    · simp [a]
    · have eq : g.op=GateOp.or := o
      simp [eq],(mono g hg).2⟩) cnt_inputs (roots fa fb)
  simpa [coneList,Circuit.size] using h

lemma coneAgree {N J : ℕ} (C : Circuit) (fa fb : Fin J → ℕ) (x y : Fin (N+N) → Bool)
    (same : ∀ i : Fin (N+N), i.val ∈ coneList N C fa fb → x i=y i) :
    ∀ r∈roots fa fb, (C.wires (List.ofFn x)).getD r false = (C.wires (List.ofFn y)).getD r false := by
  intro r hr
  apply (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2
  intro p hp
  apply same
  exact List.mem_map.mpr ⟨p,Finset.mem_toList.mpr (Finset.mem_biUnion.mpr ⟨r,hr,hp⟩),rfl⟩
theorem coneEndpoints {N j : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (fa fb : Fin j → ℕ)
    (sound : ∀ (b : Fin j) (x : Fin (N+N) → Bool), (C.wires (List.ofFn x)).getD (fa b) false = true →
       (C.wires (List.ofFn x)).getD (fb b) false = true → ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true)
    (p l : Fin N) (b : Fin j)
    (aon : (C.wires (List.ofFn (pairBits p l))).getD (fa b) false=true)
    (bon : (C.wires (List.ofFn (pairBits p l))).getD (fb b) false=true)
    (aoff : (C.wires (List.ofFn (pointBits p))).getD (fa b) false=false) :
    p ∈ pt N (coneList N C fa fb) ∧ l ∈ ln N (coneList N C fa fb) := by
  have faR : fa b ∈ roots fa fb := by simp [roots]
  have fbR : fb b ∈ roots fa fb := by simp [roots]
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra missing
    have two := coneAgree C fa fb (pairBits p l) (lineBits l) (by
      intro i hi
      have diff : i ≠ Fin.castAdd N p := by rintro rfl; exact missing hi
      by_cases line : i = Fin.natAdd N l <;> simp [pairBits,lineBits,diff,line])
    obtain ⟨q,u,_,yes,_⟩ := sound b (lineBits l) ((two _ faR).symm.trans aon) ((two _ fbR).symm.trans bon)
    have eq : Fin.castAdd N q = Fin.natAdd N l := of_decide_eq_true yes
    have val := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at val
    omega
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra missing
    have two := coneAgree C fa fb (pairBits p l) (pointBits p) (by
      intro i hi
      have diff : i ≠ Fin.natAdd N l := by rintro rfl; exact missing hi
      by_cases point : i=Fin.castAdd N p <;> simp only [pairBits,pointBits,if_neg diff,point,ite_true,ite_false,decide_true,decide_false])
    exact Bool.noConfusion (aon.symm.trans ((two _ faR).trans aoff))

end Incidence1393


namespace Incidence1393

private theorem squarePacking {N : ℕ} (X Y : Finset (Fin N)) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (noSquare : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u)) :
    (∑ l ∈ Y, (X.filter fun p => I p l).card)^2 ≤
      Y.card*((X.card*X.card-X.card)+(∑ l ∈ Y, (X.filter fun p => I p l).card)) := by
  classical
  let A (l : Fin N) := X.filter (fun p => I p l)
  have disj : (Y : Set (Fin N)).PairwiseDisjoint (fun l => (A l).offDiag) := by
    intro l _ u _ lu
    apply Finset.disjoint_left.mpr
    intro z hl hu
    obtain ⟨p,q⟩ := z
    obtain ⟨pl,ql,pq⟩ := Finset.mem_offDiag.mp hl
    obtain ⟨pu,qu,_⟩ := Finset.mem_offDiag.mp hu
    exact noSquare p q l u pq lu ⟨(Finset.mem_filter.mp pl).2, (Finset.mem_filter.mp pu).2,
      (Finset.mem_filter.mp ql).2, (Finset.mem_filter.mp qu).2⟩
  have pairs : (∑ l ∈ Y, (A l).offDiag.card) ≤ X.card*X.card-X.card := by
    rw [← Finset.card_biUnion disj, ← Finset.offDiag_card]
    apply Finset.card_le_card
    intro e he
    obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp he
    exact Finset.offDiag_mono (Finset.filter_subset _ _) hl

  have identity (l : Fin N) : (A l).card^2 = (A l).offDiag.card+(A l).card := by
    rw [Finset.offDiag_card,pow_two,Nat.sub_add_cancel (Nat.le_mul_self _)]
  have sq := sq_sum_le_card_mul_sum_sq (s:=Y) (f:=fun l => (A l).card)
  simp only [Nat.cast_id,identity,Finset.sum_add_distrib] at sq
  exact sq.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right pairs _))

private theorem algebra {a b E : ℕ} (ordered : a≤b) (small : a+b≤345282)
    (edges : E≤a*b) (sq : E^2≤b*((a*a-a)+E)) : E≤208*(a+b) := by
  have nn := Nat.le_mul_self a
  zify [nn] at *
  let v : ℤ := (a : ℤ)+b
  let z : ℤ := (b : ℤ)-a
  have vz : 0≤z := by dsimp [z]; omega
  have vn : 0≤v := by dsimp [v]; positivity
  by_cases low : v≤832
  · have h := mul_nonneg vn (sub_nonneg.mpr low)
    dsimp [v] at *
    nlinarith [sq_nonneg ((a : ℤ)-b)]
  by_cases az : a=0
  · simp [az] at edges ⊢
    omega
  have va : 0≤345282-v := by dsimp [v]; omega
  have vb : 0≤v-832 := by omega
  have aa : 0≤(a : ℤ)-1 := by omega
  have certificate :
      8*(208*v)*(208*v-b)-8*((a:ℤ)*a-a)*b =
        v^2*(345282-v)+z*v*(v-832)+2*z^2*(a-1) := by dsimp [v,z]; ring
  have cap : ((a:ℤ)*a-a)*b ≤ (208*v)*(208*v-b) := by
    nlinarith only [certificate,mul_nonneg (sq_nonneg v) va,mul_nonneg (mul_nonneg vz vn) vb,
      mul_nonneg (sq_nonneg z) aa]
  by_contra! tooBig
  change 208*v < (E:ℤ) at tooBig
  have growth : 0<((E:ℤ)-208*v)*(E+208*v-b) := by
    apply mul_pos (sub_pos.mpr tooBig)
    dsimp [v] at *
    omega
  nlinarith only [cap,sq,growth]

theorem balancedBound {N t : ℕ} (X Y : Finset (Fin N)) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (noSquare : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (support : X.card+Y.card≤2*t) (small : X.card+Y.card≤345282) :
    (∑ l ∈ Y, (X.filter fun p => I p l).card) ≤ 400*t + 16*N := by
  classical
  let E := ∑ l ∈ Y, (X.filter fun p => I p l).card
  have edge : E≤X.card*Y.card := by
    calc E ≤ ∑ _ ∈ Y, X.card := Finset.sum_le_sum (fun _ _ => Finset.card_filter_le _ _)
         _ = _ := by simp [mul_comm]
  have bound : E≤208*(X.card+Y.card) := by
    rcases le_total X.card Y.card with h | h
    · exact algebra h small edge (squarePacking X Y I noSquare)
    · have rev := squarePacking Y X (fun l p => I p l) (by
        rintro l u p q lu pq ⟨a,b,c,d⟩
        exact noSquare p q l u pq lu ⟨a,c,b,d⟩)
      have swap : (∑ p ∈ X, (Y.filter fun l => I p l).card) = E := by
        simp only [E,Finset.card_filter]
        exact Finset.sum_comm
      rw [swap] at rev
      simpa [add_comm] using algebra h (by omega) (by simpa [mul_comm] using edge) rev
  have xl : X.card ≤ N := by simpa using Finset.card_le_univ X
  have yl : Y.card ≤ N := by simpa using Finset.card_le_univ Y
  change E ≤ _
  omega

end Incidence1393

theorem Incidence1393.coneTarget : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (N ≤ 172641 ∨ Ckt.size+(Incidence1393.roots fa fb).card ≤ 345282) → (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false)).card ≤ 400 * (Ckt.size + Jn) + 16 * N := by
  classical
  intro N Jn I inst Ckt fa fb fr small noSquare mono degree sound
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false)
  let R := Incidence1393.coneList N Ckt fa fb
  let X := Incidence1393.pt N R
  let Y := Incidence1393.ln N R

  have measure : X.card+Y.card ≤ Ckt.size+(Incidence1393.roots fa fb).card :=
    (Incidence1393.both_size N R).trans (Incidence1393.coneCount N Ckt fa fb mono)
  have roots := Incidence1393.rootCount fa fb
  have total : X.card+Y.card ≤ 2*(Ckt.size+Jn) := by omega
  have xn : X.card ≤ N := by simpa using Finset.card_le_univ X
  have yn : Y.card ≤ N := by simpa using Finset.card_le_univ Y
  have estimate := Incidence1393.balancedBound X Y I noSquare total (by omega)
  have sub : E ⊆ (X ×ˢ Y).filter (fun e => I e.1 e.2) := by
    intro e he
    obtain ⟨p,l⟩ := e
    obtain ⟨edge,_,⟨b,ha,hb⟩,diag⟩ := (Finset.mem_filter.mp he).2
    have hp := Incidence1393.coneEndpoints I Ckt fa fb sound p l b ha hb (diag b ha hb).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hp,edge⟩
  have eq : ((X ×ˢ Y).filter (fun e => I e.1 e.2)).card = ∑ l ∈ Y, (X.filter fun p => I p l).card := by
    simp only [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_comm
  change E.card ≤ _
  exact (Finset.card_le_card sub).trans (eq ▸ estimate)
