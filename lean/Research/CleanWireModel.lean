import Research.CleanStarOwners

namespace PlaneResearch.CleanWireModel
open PEqualNP.CircuitLowerBounds PlaneResearch.StarOwners

abbrev Node (n : ℕ) (C : Circuit) := Fin (n+C.gates.length)
def node {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) : Node n C := ⟨n+k,by omega⟩
noncomputable def parents {n : ℕ} (C : Circuit) (w : Node n C) : Finset (Node n C) := by
  classical
  exact Finset.univ.filter (fun p => Link n C p.val w.val)
def support {n : ℕ} (C : Circuit) (w : Node n C) : Finset (Fin n) :=
  Finset.univ.filter (fun p => W C w.val (single p)=true)
noncomputable def live {n : ℕ} (C : Circuit) (out : Node n C) : Finset (Node n C) := by
  classical
  exact Finset.univ.filter (fun p => Relation.ReflTransGen (fun a b : Node n C => Link n C a.val b.val) p out)
abbrev NoSingletonAnd {n : ℕ} (C : Circuit) := ∀ k (hk : k<C.gates.length), (C.gates[k]).op=.and →
  ∀ p : Fin n, W C (n+k) (single p)=false

lemma mem_parents {n : ℕ} (C : Circuit) (w p : Node n C) :
    p ∈ parents C w ↔ Link n C p.val w.val := by classical simp [parents]

lemma gate_parent {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (p : Node n C) :
    p ∈ parents C (node C k hk) ↔ p.val<n+k ∧ p.val ∈ (C.gates[k]).inputs := by
  rw [mem_parents]
  constructor
  · rintro ⟨lt,j,g,eq,found,reads⟩
    change n+k=n+j at eq
    have jk : j=k := by omega
    subst j
    rw [List.getElem?_eq_getElem hk] at found
    cases found
    exact ⟨lt,reads⟩
  · rintro ⟨lt,reads⟩
    exact ⟨lt,k,C.gates[k],rfl,List.getElem?_eq_getElem hk,reads⟩

lemma capacity {n : ℕ} (C : Circuit) (two : ∀ g ∈ C.gates, g.inputs.length≤2) (w : Node n C) :
    (parents C w).card ≤ 2 := by
  by_cases raw : w.val<n
  · have emp : parents C w=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p h
      obtain ⟨_,j,_,eq,_,_⟩ := (mem_parents C w p).mp h
      omega
    simp [emp]
  · let k := w.val-n
    have hk : k<C.gates.length := by dsimp [k]; have := w.isLt; omega
    have eq : w=node C k hk := Fin.ext (by dsimp [node,k]; omega)
    rw [eq]
    have b : (parents C (node (n:=n) C k hk)).card ≤ (C.gates[k]).inputs.toFinset.card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro p hp
        exact List.mem_toFinset.mpr ((gate_parent C k hk p).mp hp).2
      · intro a _ b _ h; exact Fin.ext h
    exact b.trans ((List.toFinset_card_le _).trans (two _ (List.getElem_mem ..)))

lemma live_root {n : ℕ} (C : Circuit) (o : Node n C) : o ∈ live C o := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩

lemma live_parent {n : ℕ} (C : Circuit) (o w p : Node n C) (hw : w ∈ live C o)
    (hp : p ∈ parents C w) : p ∈ live C o := by
  classical
  have path := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.head ((mem_parents C w p).mp hp) path⟩

lemma has_reader {n : ℕ} (C : Circuit) (o w : Node n C) (hw : w ∈ live C o) :
    w=o ∨ ∃ j ∈ live C o, w ∈ parents C j := by
  classical
  rcases (Finset.mem_filter.mp hw).2.cases_head with eq|⟨j,link,path⟩
  · exact Or.inl eq
  · exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,path⟩,(mem_parents C j w).mpr link⟩

lemma raw_set {n : ℕ} (C : Circuit) (w : Node n C) (hi : w.val<n) :
    support C w = {⟨w.val,hi⟩} := by
  ext p
  let q : Fin n := ⟨w.val,hi⟩
  change p ∈ Finset.univ.filter (fun p => W C q.val (single p)=true) ↔ p ∈ ({q} : Finset (Fin n))
  simp [input,single,eq_comm]

lemma and_set {n : ℕ} (C : Circuit) (quiet : NoSingletonAnd (n:=n) C) (k : ℕ) (hk : k<C.gates.length)
    (and : (C.gates[k]).op=.and) : support C (node (n:=n) C k hk)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have yes := (Finset.mem_filter.mp hp).2
  change W C (n+k) (single p)=true at yes
  rw [quiet k hk and p] at yes
  contradiction

lemma or_set {n : ℕ} (C : Circuit) (k : ℕ) (hk : k<C.gates.length) (op : (C.gates[k]).op=.or) :
    support C (node (n:=n) C k hk) = (parents C (node C k hk)).biUnion (support C) := by
  classical
  ext p
  change (p ∈ Finset.univ.filter (fun p => W C (n+k) (single p)=true)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,or_on C k hk op,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,hj,lt,on'⟩
    let v : Node n C := ⟨j,by omega⟩
    exact ⟨v,(gate_parent C k hk v).mpr ⟨lt,hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,on'⟩⟩
  · rintro ⟨v,hv,pv⟩
    have h := (gate_parent C k hk v).mp hv
    exact ⟨v.val,h.2,h.1,(Finset.mem_filter.mp pv).2⟩

noncomputable def family {n : ℕ} (C : Circuit) (out : Node n C) :=
  (live C out).image (support C)
noncomputable def forks {n : ℕ} (C : Circuit) (out : Node n C) : Finset (Node n C) := by
  classical
  exact (live C out).filter (fun w => n≤w.val ∧ (support C w).Nonempty ∧ ∀ p ∈ parents C w, (support C p).Nonempty)

/-- A set of at least two singleton responses first appears at an OR with
two nonempty, strictly smaller parent supports. -/
theorem first_union {n : ℕ} (C : Circuit) (out : Node n C) (ops : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or)
    (two : ∀ g ∈ C.gates, g.inputs.length≤2) (quiet : NoSingletonAnd (n:=n) C)
    (s : Finset (Fin n)) (made : s ∈ family C out) (big : 1<s.card) :
    (∃ w ∈ forks C out, support C w=s) ∧
    ∃ a ∈ family C out, ∃ b ∈ family C out, a.card<s.card ∧ b.card<s.card ∧ a ∪ b=s := by
  classical
  let F := (live C out).filter (fun w => support C w=s)
  obtain ⟨w₀,l₀,e₀⟩ := Finset.mem_image.mp made
  have non : F.Nonempty := ⟨w₀,Finset.mem_filter.mpr ⟨l₀,e₀⟩⟩
  obtain ⟨w,wf,minimal⟩ := Finset.exists_min_image F Fin.val non
  obtain ⟨lw,sw⟩ := Finset.mem_filter.mp wf
  have ng : n≤w.val := by
    by_contra! raw
    have card := congrArg Finset.card ((raw_set C w raw).symm.trans sw)
    simp at card
    omega
  let k := w.val-n
  have hk : k<C.gates.length := by dsimp [k]; have := w.isLt; omega
  have eq : w=node C k hk := Fin.ext (by dsimp [node,k]; omega)
  have union : (parents C w).biUnion (support C)=s := by
    rcases ops C.gates[k] (List.getElem_mem ..) with a|o
    · have emp : s=∅ := sw.symm.trans (eq ▸ and_set C quiet k hk a)
      simp [emp] at big
    · rw [eq,←or_set C k hk o,←eq,sw]
  have small (v : Node n C) (hv : v ∈ parents C w) : (support C v).card<s.card := by
    have sub : support C v ⊆ s := by
      rw [←union]
      exact Finset.subset_biUnion_of_mem (support C) hv
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => by
      have ge := minimal v (Finset.mem_filter.mpr ⟨live_parent C out w v lw hv,e⟩)
      have lt := ((mem_parents C w v).mp hv).1
      omega⟩)
  have cap := capacity C two w
  have twoP : (parents C w).card=2 := by
    by_contra ne
    have one : (parents C w).card≤1 := by omega
    rcases (parents C w).eq_empty_or_nonempty with empty|⟨v,hv⟩
    · simp [empty] at union; simp [←union] at big
    · have singleton : parents C w={v} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv,fun z hz => Finset.card_le_one.mp one _ hz _ hv⟩
      have h := small v hv
      simp [singleton] at union
      rw [union] at h
      exact (Nat.lt_irrefl _ h).elim
  obtain ⟨a,b,ab,pair⟩ := Finset.card_eq_two.mp twoP
  have pa : a ∈ parents C w := by simp [pair]
  have pb : b ∈ parents C w := by simp [pair]
  have combo : support C a ∪ support C b = s := by simpa [pair] using union
  have sa := small a pa
  have sb := small b pb
  have nonA : (support C a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.empty_union] at combo
    rw [combo] at sb
    exact Nat.lt_irrefl _ sb
  have nonB : (support C b).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.union_empty] at combo
    rw [combo] at sa
    exact Nat.lt_irrefl _ sa
  refine ⟨⟨w,Finset.mem_filter.mpr ⟨lw,ng,?_,?_⟩,sw⟩,
    support C a,Finset.mem_image_of_mem _ (live_parent C out w a lw pa),
    support C b,Finset.mem_image_of_mem _ (live_parent C out w b lw pb),sa,sb,combo⟩
  · rw [sw]; exact Finset.card_pos.mp (by omega)
  · intro p hp
    rw [pair] at hp
    rcases Finset.mem_insert.mp hp with rfl|h
    · exact nonA
    · exact Finset.mem_singleton.mp h ▸ nonB

end PlaneResearch.CleanWireModel
