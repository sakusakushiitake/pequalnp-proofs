import Mathlib

namespace LineTestsMinimal

variable {α : Type*} [DecidableEq α] [Fintype α]

def hits (S R : Finset α) : Prop := ∃ a ∈ S, a ∈ R
def target (T M S : Finset α) : Prop := hits S T ∧ hits S M
def mono (f : Finset α → Prop) : Prop := ∀ ⦃S U⦄, S ⊆ U → f S → f U
def complete (T M : Finset α) (Q : Set (Finset α)) : Prop :=
  ∀ f : Finset α → Prop, mono f → (∀ S ∈ Q, f S ↔ target T M S) →
    ∀ S, hits S T → (f S ↔ hits S M)

omit [DecidableEq α] [Fintype α] in
private theorem hits_mono {S U R : Finset α} (h : S ⊆ U) : hits S R → hits U R := by
  rintro ⟨a,ha,hr⟩
  exact ⟨a,h ha,hr⟩

omit [DecidableEq α] [Fintype α] in
private theorem target_mono (T M : Finset α) : mono (target T M) :=
  fun _ _ h ⟨t,m⟩ => ⟨hits_mono h t,hits_mono h m⟩

private theorem force_positive {T M S : Finset α} {Q : Set (Finset α)}
    (hq : complete T M Q) (pos : target T M S)
    (minim : ∀ U ⊆ S, target T M U → U = S) : S ∈ Q := by
  classical
  by_contra absent
  let f := fun U => target T M U ∧ U ≠ S
  have hm : mono f := by
    rintro U V uv ⟨good,ne⟩
    refine ⟨target_mono T M uv good,?_⟩
    rintro rfl
    exact ne (minim U uv good)
  have agree : ∀ U ∈ Q, f U ↔ target T M U := by
    intro U hu
    have ne : U ≠ S := fun eq => absent (eq ▸ hu)
    simp [f,ne]
  exact ((hq f hm agree S pos.1).mpr pos.2).2 rfl

private theorem force_complement {T M : Finset α} {Q : Set (Finset α)}
    (hq : complete T M Q) (outside : ¬ T ⊆ M) : Mᶜ ∈ Q := by
  classical
  obtain ⟨t,ht,notM⟩ := Finset.not_subset.mp outside
  have dom : hits Mᶜ T := ⟨t,Finset.mem_compl.mpr notM,ht⟩
  by_contra absent
  let f := fun U => target T M U ∨ Mᶜ ⊆ U
  have mon : mono f := by
    rintro U V uv (good|large)
    · exact Or.inl (target_mono T M uv good)
    · exact Or.inr (large.trans uv)
  have agree : ∀ U ∈ Q, f U ↔ target T M U := by
    intro U hu
    refine ⟨?_,Or.inl⟩
    rintro (good|large)
    · exact good
    · refine ⟨hits_mono large dom,?_⟩
      by_contra empty
      have sub : U ⊆ Mᶜ := by
        intro p hp
        exact Finset.mem_compl.mpr (fun hm => empty ⟨p,hp,hm⟩)
      exact absent (Finset.Subset.antisymm sub large ▸ hu)
  obtain ⟨p,hp,hm⟩ := (hq f mon agree Mᶜ dom).mp (Or.inr (Finset.Subset.refl _))
  exact (Finset.mem_compl.mp hp) hm

theorem characterization (T M : Finset α) (outside : ¬ T ⊆ M) (Q : Set (Finset α)) :
    complete T M Q ↔ (∀ a ∈ T ∩ M, {a} ∈ Q) ∧
      (∀ a ∈ T \ M, ∀ b ∈ M \ T, {a,b} ∈ Q) ∧ Mᶜ ∈ Q := by
  classical
  constructor
  · intro hq
    refine ⟨?_,?_,force_complement hq outside⟩
    · intro a ha
      obtain ⟨atT,atM⟩ := Finset.mem_inter.mp ha
      apply force_positive hq ⟨⟨a,by simp,atT⟩,⟨a,by simp,atM⟩⟩
      rintro U sub ⟨⟨v,hv,_⟩,_⟩
      have eq := Finset.mem_singleton.mp (sub hv)
      exact Finset.Subset.antisymm sub (Finset.singleton_subset_iff.mpr (eq ▸ hv))
    · intro a ha b hb
      obtain ⟨atT,notM⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨atM,notT⟩ := Finset.mem_sdiff.mp hb
      apply force_positive hq ⟨⟨a,by simp,atT⟩,⟨b,by simp,atM⟩⟩
      rintro U sub ⟨⟨u,hu,ut⟩,⟨v,hv,vm⟩⟩
      have ua : u=a := by
        have huv : u=a ∨ u=b := by simpa using sub hu
        exact huv.resolve_right (fun eq => notT (eq ▸ ut))
      have vb : v=b := by
        have hvv : v=a ∨ v=b := by simpa using sub hv
        exact hvv.resolve_left (fun eq => notM (eq ▸ vm))
      apply Finset.Subset.antisymm sub
      intro z hz
      rcases (show z=a ∨ z=b by simpa using hz) with rfl|rfl
      · exact ua ▸ hu
      · exact vb ▸ hv
  · rintro ⟨one,two,last⟩ f mon agree S dom
    constructor
    · intro fs
      by_contra empty
      have sub : S ⊆ Mᶜ := by
        intro p hp
        exact Finset.mem_compl.mpr (fun hm => empty ⟨p,hp,hm⟩)
      obtain ⟨_,⟨p,hp,hm⟩⟩ := (agree _ last).mp (mon sub fs)
      exact (Finset.mem_compl.mp hp) hm
    · rintro ⟨b,bs,bm⟩
      obtain ⟨a,as',atT⟩ := dom
      have single (z : α) (sz : z ∈ S) (tz : z ∈ T) (mz : z ∈ M) : f S :=
        mon (Finset.singleton_subset_iff.mpr sz)
          ((agree _ (one z (Finset.mem_inter.mpr ⟨tz,mz⟩))).mpr
            ⟨⟨z,by simp,tz⟩,⟨z,by simp,mz⟩⟩)
      by_cases am : a ∈ M
      · exact single a as' atT am
      by_cases bt : b ∈ T
      · exact single b bs bt bm
      have test := two a (Finset.mem_sdiff.mpr ⟨atT,am⟩) b (Finset.mem_sdiff.mpr ⟨bm,bt⟩)
      have sub : ({a,b} : Finset α) ⊆ S := by
        intro z hz
        rcases (show z=a ∨ z=b by simpa using hz) with rfl|rfl
        · exact as'
        · exact bs
      exact mon sub
        ((agree _ test).mpr ⟨⟨a,by simp,atT⟩,⟨b,by simp,bm⟩⟩)

def suite {ι : Type*} [Fintype ι] (T : Finset α) (M : ι → Finset α) : Finset (Finset α) :=
  (T.image fun a => {a}) ∪
    ((T ×ˢ Tᶜ).image fun p : α × α => {p.1,p.2}) ∪
    (Finset.univ.image fun i => (M i)ᶜ)

theorem family {ι : Type*} [Fintype ι] (T : Finset α) (M : ι → Finset α)
    (outside : ∀ i, ¬ T ⊆ M i) (covered : ∀ a ∈ T, ∃ i, a ∈ M i)
    (separate : ∀ a ∈ T, ∀ b ∉ T, ∃ i, b ∈ M i ∧ a ∉ M i) (Q : Finset (Finset α)) :
    (∀ i, complete T (M i) (↑Q)) ↔ suite T M ⊆ Q := by
  classical
  constructor
  · intro h S hs
    rcases Finset.mem_union.mp hs with h12|h3
    · rcases Finset.mem_union.mp h12 with h1|h2
      · obtain ⟨a,atT,rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨i,am⟩ := covered _ atT
        exact ((characterization T (M i) (outside i) _).mp (h i)).1 a (Finset.mem_inter.mpr ⟨atT,am⟩)
      · obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp h2
        obtain ⟨atT,bt⟩ := Finset.mem_product.mp hab
        obtain ⟨i,bm,am⟩ := separate _ atT _ (Finset.mem_compl.mp bt)
        exact ((characterization T (M i) (outside i) _).mp (h i)).2.1 a
          (Finset.mem_sdiff.mpr ⟨atT,am⟩) b (Finset.mem_sdiff.mpr ⟨bm,Finset.mem_compl.mp bt⟩)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h3
      exact ((characterization T (M i) (outside i) _).mp (h i)).2.2
  · intro h i
    apply (characterization T (M i) (outside i) _).mpr
    refine ⟨?_,?_,?_⟩
    · intro a ha
      exact h (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨a,(Finset.mem_inter.mp ha).1,rfl⟩)))
    · intro a ha b hb
      exact h (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
          ⟨(Finset.mem_sdiff.mp ha).1,Finset.mem_compl.mpr (Finset.mem_sdiff.mp hb).2⟩,rfl⟩)))
    · exact h (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem suite_card {ι : Type*} [Fintype ι] (T : Finset α) (M : ι → Finset α)
    (distinct : Function.Injective M) (wide : ∀ i, 3 ≤ (M i)ᶜ.card) :
    (suite T M).card = T.card + T.card * (Fintype.card α - T.card) + Fintype.card ι := by
  classical
  let sing := T.image (fun a => ({a} : Finset α))
  let pair := (T ×ˢ Tᶜ).image (fun p : α × α => ({p.1,p.2} : Finset α))
  let comp := Finset.univ.image (fun i => (M i)ᶜ)
  have cs : sing.card = T.card := Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_inj.mp h)
  have pair_two {S : Finset α} (hs : S ∈ pair) : S.card = 2 := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨atT,bt⟩ := Finset.mem_product.mp hab
    exact Finset.card_pair (fun eq => (Finset.mem_compl.mp bt) (eq ▸ atT))
  have cp : pair.card = T.card * (Fintype.card α - T.card) := by
    change ((T ×ˢ Tᶜ).image _).card = _
    rw [Finset.card_image_of_injOn,Finset.card_product,Finset.card_compl]
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
    obtain ⟨atT,bt⟩ := Finset.mem_product.mp hab
    obtain ⟨ct,dt⟩ := Finset.mem_product.mp hcd
    change ({a,b} : Finset α) = {c,d} at eq
    have ah : a ∈ ({c,d} : Finset α) := by rw [← eq]; simp
    have bh : b ∈ ({c,d} : Finset α) := by rw [← eq]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at ah bh
    exact Prod.ext (ah.resolve_right (fun e => Finset.mem_compl.mp dt (e ▸ atT)))
      (bh.resolve_left (fun e => Finset.mem_compl.mp bt (e ▸ ct)))
  have cc : comp.card = Fintype.card ι := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ (fun a b h => distinct (compl_injective h)),Finset.card_univ]
  have ds : Disjoint sing pair := by
    apply Finset.disjoint_left.mpr
    intro S hs hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    simpa using pair_two hp
  have dc : Disjoint (sing ∪ pair) comp := by
    apply Finset.disjoint_left.mpr
    intro S hs hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    have hi := wide i
    rcases Finset.mem_union.mp hs with hs|hp
    · obtain ⟨a,_,eq⟩ := Finset.mem_image.mp hs
      rw [← eq,Finset.card_singleton] at hi
      omega
    · have h2 := pair_two hp
      omega
  change ((sing ∪ pair) ∪ comp).card = _
  rw [Finset.card_union_of_disjoint dc,Finset.card_union_of_disjoint ds,cs,cp,cc]

def line21 (t : Fin 21) : Finset (Fin 21) := {t,t+1,t+4,t+14,t+16}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem geometry21 :
    (∀ a b : Fin 21, a ≠ b → ∃ i, b ∈ line21 i ∧ a ∉ line21 i) ∧
    (∀ a b : Fin 21, line21 a = line21 b → a=b) ∧
    (∀ i : Fin 21, (line21 i).card = 5) := by decide +kernel

theorem orderFour_minimum (T : Finset (Fin 21)) (three : T.card = 3)
    (noncollinear : ∀ i, ¬ T ⊆ line21 i) :
    (∀ i, complete T (line21 i) (↑(suite T line21))) ∧
    (suite T line21).card = 78 ∧
    ∀ Q : Finset (Finset (Fin 21)), (∀ i, complete T (line21 i) (↑Q)) → 78 ≤ Q.card := by
  have criterion := family T line21 noncollinear
    (fun a _ => ⟨a,by simp [line21]⟩)
    (fun a ha b hb => geometry21.1 a b (fun eq => hb (eq ▸ ha)))
  have card : (suite T line21).card = 78 := by
    rw [suite_card T line21 (fun _ _ h => geometry21.2.1 _ _ h)
      (fun i => by rw [Finset.card_compl,geometry21.2.2]; decide),three]
    decide
  refine ⟨(criterion _).mpr (Finset.Subset.refl _),card,fun Q good => ?_⟩
  rw [← card]
  exact Finset.card_le_card ((criterion _).mp good)

end LineTestsMinimal
