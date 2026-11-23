import Research.SideTables

namespace PlaneResearch.TableGateSearch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PlaneResearch.SideTables

def next {d : ℕ} (p : List (Table d)) : List (Table d) :=
  p.flatMap fun a => (~~~a)::(p.flatMap fun b => [a &&& b,a ||| b])

def can {d : ℕ} (f : Table d) : ℕ → List (Table d) → Bool
  | 0,p => p.contains f
  | k+1,p => can f k p || (next p).any (fun y => !(p.contains y) && can f k (y::p))

lemma step {d : ℕ} (p : List (Table d)) {a b f : Table d}
    (ha : a ∈ p) (hb : b ∈ p) (h : recipe f a b) : f ∈ next p := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,?_⟩
  rcases h with rfl|rfl|rfl
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp⟩)
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp⟩)
  · exact List.mem_cons_self

theorem complete {d : ℕ} (f : Table d) : ∀ k (gs : List Gate) (w p : List (Table d)),
    FanInTwo ⟨gs,0⟩ → gs.length≤k → 0 ∈ p → top d ∈ p → (∀ x ∈ w, x ∈ p) →
    f ∈ run gs w → can f k p=true := by
  intro k
  induction k with
  | zero =>
    intro gs w p _ len _ _ inc hit
    have emp : gs=[] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    exact List.contains_iff_mem.mpr (inc _ hit)
  | succ k ih =>
    intro gs w p ok len zero top' inc hit
    apply Bool.or_eq_true_iff.mpr
    cases gs with
    | nil => exact Or.inl (ih [] w p ok (by simp) zero top' inc hit)
    | cons g tail =>
      let v := gateVal g w
      have tailok : FanInTwo ⟨tail,0⟩ := fun a ha => ok a (List.mem_cons_of_mem _ ha)
      have tailLen : tail.length≤k := by simpa using len
      change f ∈ run tail (w++[v]) at hit
      by_cases known : v ∈ p
      · refine Or.inl (ih tail _ p tailok tailLen zero top' ?_ hit)
        intro x hx
        rcases List.mem_append.mp hx with h|h
        · exact inc _ h
        · exact List.mem_singleton.mp h ▸ known
      · have vz : v ≠ 0 := fun h => known (h ▸ zero)
        have vt : v ≠ top d := fun h => known (h ▸ top')
        have fresh : v ∉ w := fun h => known (inc _ h)
        have single : FanInTwo ⟨[g],0⟩ := by
          intro a ha
          obtain rfl := List.mem_singleton.mp ha
          exact ok a List.mem_cons_self
        obtain ⟨a,b,ha,hb,af,bf,rec⟩ := first_recipe [g] w v single vz vt fresh (by simp [run,v])
        have parent (a : Table d) (h : a ∈ run [g] w ∨ a=0) (ne : a ≠ v) : a ∈ p := by
          rcases h with h|rfl
          · change a ∈ w++[v] at h
            rcases List.mem_append.mp h with hx|hv
            · exact inc _ hx
            · exact (ne (List.mem_singleton.mp hv)).elim
          · exact zero
        refine Or.inr (List.any_eq_true.mpr ⟨v,step p (parent _ ha af) (parent _ hb bf) rec,?_⟩)
        apply Bool.and_eq_true_iff.mpr
        refine ⟨by simpa using known,ih tail _ _ tailok tailLen (List.mem_cons_of_mem _ zero) (List.mem_cons_of_mem _ top') ?_ hit⟩
        intro x hx
        rcases List.mem_append.mp hx with h|h
        · exact List.mem_cons_of_mem _ (inc _ h)
        · simp [List.mem_singleton.mp h]

theorem sampled_lower {n d k : ℕ} (f : (Fin n → Bool) → Bool) (T : Table d)
    (w p : List (Table d)) (x : Fin d → Fin n → Bool)
    (inputs : ∀ j : Fin d, w.map (fun z => z.getLsbD j.val)=List.ofFn (x j))
    (target : ∀ j : Fin d, f (x j)=T.getLsbD j.val)
    (raw : ∀ v ∈ w, v ∈ p) (zero : 0 ∈ p) (top' : top d ∈ p)
    (nz : T ≠ 0) (check : can T k p=false) : ¬HasCircuitSize n f k := by
  rintro ⟨C,ok,size,ev⟩
  have eq : (run C.gates w).getD C.output 0=T := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have bits := wire_bits C.gates w ⟨i,hi⟩ C.output ok
    rw [inputs ⟨i,hi⟩] at bits
    exact bits.trans ((ev _).trans (target _))
  have valid : C.output < (run C.gates w).length := by
    by_contra! bad
    rw [List.getD_eq_default _ _ bad] at eq
    exact nz eq.symm
  have mem : T ∈ run C.gates w := by
    rw [←eq,List.getD_eq_getElem _ _ valid]
    exact List.getElem_mem ..
  have sat := complete T k C.gates w p ok size zero top' raw mem
  exact Bool.noConfusion (sat.symm.trans check)

end PlaneResearch.TableGateSearch
