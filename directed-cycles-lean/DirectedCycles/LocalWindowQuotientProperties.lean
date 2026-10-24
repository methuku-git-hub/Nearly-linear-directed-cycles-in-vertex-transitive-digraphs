import DirectedCycles.LocalWindowQuotientAlgebra
import DirectedCycles.LocalApproximateRestriction

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace EquivalenceWindow
variable {G : Type*} {L : LocalGroupAlgebra G} {S W : Set G}
    (C : L.EquivalenceWindow S) (hWS : W ⊆ S)
    (hW1 : L.one ∈ W) (hWi : ∀ x ∈ W, L.inv x ∈ W)
    (hdom : L.AllProductsDefined W 3) (hW3 : L.wordPower W 3 ⊆ S)

noncomputable def finiteImage (B : Finset G) : Finset (C.Carrier hWS) := by
  classical
  exact (B.subtype (· ∈ W)).image (C.project hWS)

/-- Restriction followed by the actual window projection preserves the full
finite approximate-group structure and its original covering parameter. -/
theorem finiteImage_approximate {K : ℕ} {B : Finset G}
    (hB : IsLocalFiniteApproximateGroup L K B)
    (hsmall : ∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ W) :
    IsLocalFiniteApproximateGroup (C.algebra hWS hW1 hWi hdom hW3) K (C.finiteImage hWS B) := by
  classical
  exact (hB.restrict W hW1 hWi hsmall).image (C.projectionHom hWS hW1 hWi hdom hW3)

/-- Fibre differences inject into the prescribed finite set, using local
cancellation. The finite set need not be a subgroup. -/
theorem projection_card_bound (hc : L.Cancellative) (B : Finset W) (R : Finset G)
    (hdiff : ∀ a b : W, C.Rel a.val b.val → ∃ p ∈ R, L.mulRel a.val (L.inv b.val) p) :
    B.card ≤ (by classical exact (B.image (C.project hWS)).card) * R.card := by
  classical
  let Q := B.image (C.project hWS)
  have hex : ∀ y : Q, ∃ b : B, C.project hWS b.val = y.val := by
    intro y
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp y.property
    exact ⟨⟨b,hb⟩,he⟩
  choose b hb using hex
  let qi : B → Q := fun a => ⟨C.project hWS a.val,Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  have hw : ∀ a : B, ∃ p ∈ R, L.mulRel a.val.val (L.inv (b (qi a)).val.val) p := by
    intro a
    exact hdiff a.val (b (qi a)).val (Quotient.exact (hb (qi a)).symm)
  choose p hp hmul using hw
  let f : B → Q × R := fun a => (qi a,⟨p a,hp a⟩)
  have hf : Function.Injective f := by
    intro a c he
    have hq : qi a = qi c := congrArg Prod.fst he
    have he' : p a = p c := congrArg (fun z : Q × R => z.2.val) he
    have ha := hmul a
    rw [hq,he'] at ha
    exact Subtype.ext (Subtype.ext (hc.right_cancel ha (hmul c)))
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_coe,Q] using hcard

theorem finiteImage_card_bound (hc : L.Cancellative) (B R : Finset G)
    (hB : (B : Set G) ⊆ W)
    (hdiff : ∀ a b : W, C.Rel a.val b.val → ∃ p ∈ R, L.mulRel a.val (L.inv b.val) p) :
    B.card ≤ (C.finiteImage hWS B).card * R.card := by
  classical
  have hb : (B.subtype (· ∈ W)).card = B.card := by
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr hB]
  have h := C.projection_card_bound hWS hc (B.subtype (· ∈ W)) R hdiff
  simpa only [hb,finiteImage] using h
end EquivalenceWindow
end LocalGroupAlgebra
end DirectedCycles
