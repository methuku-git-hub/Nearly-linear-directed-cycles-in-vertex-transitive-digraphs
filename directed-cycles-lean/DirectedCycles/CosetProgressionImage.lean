import DirectedCycles.CosetProgressionHomWords

set_option autoImplicit false
namespace DirectedCycles

/-- Map the actual subgroup, finite subgroup and generators through a
homomorphism. The normality and generation assertions are derived in the
image subgroup, rather than assumed in the full target group. -/
def imageCosetNilprogression {G H : Type*} [Group G] [Group H]
    (f : G →* H) {r c : ℕ} (P : CosetNilprogression G r c) : CosetNilprogression H r c := by
  let U := P.U.map f
  let K := P.H.map f
  let F := f.subgroupMap P.U
  have hF : Function.Surjective F := f.subgroupMap_surjective P.U
  have hK : K.subgroupOf U = (P.H.subgroupOf P.U).map F := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      exact ⟨⟨y,P.hHU hy⟩,hy,Subtype.ext he⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y.val,hy,congrArg (fun z : U => z.val) he⟩
  have hnormal : (K.subgroupOf U).Normal := by
    rw [hK]
    exact P.normal.map F hF
  let g : Fin r → U := fun i => F (P.generators i)
  have hgen : Subgroup.closure ((K.subgroupOf U : Set U) ∪ Set.range g) = ⊤ := by
    have hh := image_generating_set F hF _ P.generates
    rw [Set.image_union,← Set.range_comp'] at hh
    change Subgroup.closure (((P.H.subgroupOf P.U).map F : Set U) ∪ Set.range g) = ⊤ at hh
    rwa [← hK] at hh
  refine ⟨U,K,Subgroup.map_mono P.hHU,hnormal,g,P.lengths,P.lengths_pos,hgen,?_⟩
  let := hnormal
  intro w hw
  have hp := P.commutators w hw
  rw [← w.map_eval (QuotientGroup.mk' (P.H.subgroupOf P.U)) P.generators] at hp
  have hmem : w.eval P.generators ∈ P.H.subgroupOf P.U :=
    (QuotientGroup.eq_one_iff _).1 hp
  rw [← w.map_eval (QuotientGroup.mk' (K.subgroupOf U)) g]
  apply (QuotientGroup.eq_one_iff _).2
  rw [hK]
  exact ⟨w.eval P.generators,hmem,w.map_eval F P.generators⟩

/-- The image construction preserves the carrier exactly, with the same
rank, step and coordinate lengths. -/
theorem imageCosetNilprogression_carrier {G H : Type*} [Group G] [Group H]
    (f : G →* H) {r c : ℕ} (P : CosetNilprogression G r c) :
    (imageCosetNilprogression f P).carrier = f '' P.carrier := by
  ext z
  change (∃ h : P.H.map f, ∃ w : List (Fin r × Bool),
    (∀ i, w.countP (fun a => a.1 = i) ≤ P.lengths i) ∧
      h.val*signedWordValue (fun i => f (P.generators i).val) w = z) ↔ _
  constructor
  · rintro ⟨h,w,hw,hz⟩
    obtain ⟨k,hk,hfk⟩ := h.property
    refine ⟨k*signedWordValue (fun i => (P.generators i).val) w,⟨⟨k,hk⟩,w,hw,rfl⟩,?_⟩
    rw [map_mul,map_signedWordValue,hfk]
    exact hz
  · rintro ⟨z,⟨h,w,hw,hz⟩,rfl⟩
    refine ⟨⟨f h.val,⟨h.val,h.property,rfl⟩⟩,w,hw,?_⟩
    have hh := congrArg f hz
    rwa [map_mul,map_signedWordValue] at hh

/-- Embedding a finite ambient subgroup back into the original group
preserves the density factor and the exact coset-nilprogression bounds. -/
theorem coset_progression_image_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {r c : ℕ} (P : CosetNilprogression G r c)
    (A : Set G) (hPA : P.carrier ⊆ A) (a J : ℕ) (hcard : a ≤ J*Nat.card P.carrier) :
    ∃ Q : CosetNilprogression H r c, Q.carrier ⊆ f '' A ∧ a ≤ J*Nat.card Q.carrier := by
  refine ⟨imageCosetNilprogression f P,?_,?_⟩
  · rw [imageCosetNilprogression_carrier]
    exact Set.image_mono hPA
  · rw [imageCosetNilprogression_carrier,Nat.card_image_of_injective hf]
    exact hcard
end DirectedCycles
