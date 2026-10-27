module

public import DirectedCycles.LocalQuotientHom

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- Fibres of the actual window projection inject into P by taking the
relative difference from a chosen representative. This gives the finite
cardinality bound without replacing P by its generated global subgroup. -/
theorem window_projection_card_bound [DecidableEq (hP.WindowQuotient hW1 hWi hW6)]
    (B : Finset W) (R : Finset G) (hR : P ⊆ (R : Set G)) :
    B.card ≤ (B.image (hP.windowMk hW1 hWi hW6)).card * R.card := by
  classical
  let q := hP.windowMk hW1 hWi hW6
  let Q := B.image q
  have hex : ∀ y : Q, ∃ b : B, q b.val = y.val := by
    intro y
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp y.property
    exact ⟨⟨b,hb⟩,he⟩
  choose b hb using hex
  let qi : B → Q := fun a => ⟨q a.val,Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  have hd : ∀ a : B, a.val.val * (b (qi a)).val.val⁻¹ ∈ R := by
    intro a
    apply hR
    apply (hP.window_quotient_eq_iff hW1 hWi hW6 _ _).1
    exact (hb (qi a)).symm
  let f : B → Q × R := fun a => (qi a,⟨a.val.val*(b (qi a)).val.val⁻¹,hd a⟩)
  have hf : Function.Injective f := by
    intro a c he
    have hq : qi a = qi c := congrArg Prod.fst he
    have hp := congrArg (fun z : Q × R => z.2.val) he
    change a.val.val*(b (qi a)).val.val⁻¹ = c.val.val*(b (qi c)).val.val⁻¹ at hp
    rw [hq] at hp
    exact Subtype.ext (Subtype.ext (mul_right_cancel hp))
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_coe,Q] using hcard
end LocalNormalSet
end DirectedCycles

namespace DirectedCycles
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

/-- The actual finite image in the window quotient. -/
noncomputable def finiteWindowImage (B : Finset G) : Finset (hP.WindowQuotient hW1 hWi hW6) := by
  classical
  exact (B.subtype (· ∈ W)).image (hP.windowMk hW1 hWi hW6)

theorem finiteWindowImage_card_bound (B R : Finset G) (hB : (B : Set G) ⊆ W)
    (hR : P ⊆ (R : Set G)) :
    B.card ≤ (hP.finiteWindowImage hW1 hWi hW6 B).card * R.card := by
  classical
  have h := hP.window_projection_card_bound hW1 hWi hW6 (B.subtype (· ∈ W)) R hR
  have he : (B.subtype (· ∈ W)).card = B.card := by
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr hB]
  simpa only [he,finiteWindowImage] using h
end LocalNormalSet
end DirectedCycles
