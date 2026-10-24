import DirectedCycles.LocalNormalSubgroupQuotient
import DirectedCycles.LocalApproximateRestriction

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace NormalSubgroupWindow
variable {G : Type*} {L : LocalGroupAlgebra G} {H S : Set G}
    (W : L.NormalSubgroupWindow H S) (hd : L.DivisionClosed) (hr : L.Reversible)

/-- The actual finite image under the local subgroup quotient projection. -/
noncomputable def finiteImage (B : Finset G) : Finset (W.congruence hd hr).Carrier := by
  classical
  exact (B.subtype (· ∈ S)).image (W.congruence hd hr).project

/-- Every quotient fibre injects into H using a subgroup multiplier from one
chosen representative. Functionality of local multiplication proves the
injection, without invoking any ambient global group law. -/
theorem projection_card_bound [DecidableEq (W.congruence hd hr).Carrier]
    (B : Finset S) (R : Finset G) (hR : H ⊆ (R : Set G)) :
    B.card ≤ (B.image (W.congruence hd hr).project).card * R.card := by
  classical
  let C := W.congruence hd hr
  let Q := B.image C.project
  have hex : ∀ y : Q, ∃ b : B, C.project b.val = y.val := by
    intro y
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp y.property
    exact ⟨⟨b,hb⟩,he⟩
  choose b hb using hex
  let qi : B → Q := fun a => ⟨C.project a.val,Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  have hw : ∀ a : B, ∃ h ∈ R, L.mulRel h (b (qi a)).val.val a.val.val := by
    intro a
    have he : C.project a.val = C.project (b (qi a)).val := (hb (qi a)).symm
    obtain ⟨h,hh,hm⟩ := Quotient.exact he
    exact ⟨h,hR hh,hm⟩
  choose h hh hm using hw
  let f : B → Q × R := fun a => (qi a,⟨h a,hh a⟩)
  have hf : Function.Injective f := by
    intro a c he
    have hq : qi a = qi c := congrArg Prod.fst he
    have hp : h a = h c := congrArg (fun z : Q × R => z.2.val) he
    have ha := hm a
    rw [hq,hp] at ha
    exact Subtype.ext (Subtype.ext (L.unique ha (hm c)))
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_coe,Q] using hcard

theorem finiteImage_card_bound (B R : Finset G) (hB : (B : Set G) ⊆ S)
    (hR : H ⊆ (R : Set G)) :
    B.card ≤ (W.finiteImage hd hr B).card * R.card := by
  classical
  have hb : (B.subtype (· ∈ S)).card = B.card := by
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr hB]
  have h := W.projection_card_bound hd hr (B.subtype (· ∈ S)) R hR
  simpa only [hb,finiteImage] using h

/-- The actual quotient of a local approximate group has the same covering
constant once all 200 required source word values lie in the window. -/
theorem finiteImage_approximate {K : ℕ} {B : Finset G}
    (hB : IsLocalFiniteApproximateGroup L K B)
    (hS : ∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ S) :
    IsLocalFiniteApproximateGroup (W.congruence hd hr).algebra K (W.finiteImage hd hr B) := by
  classical
  exact (hB.restrict S W.one_mem W.inv_mem hS).image (W.congruence hd hr).projectionHom
end NormalSubgroupWindow
end LocalGroupAlgebra
end DirectedCycles
