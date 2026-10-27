module

public import DirectedCycles.LocalCongruenceDescent
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The internal compact/open sandwich property is preserved by a surjective
quotient map once internal images are proved internal. This lemma records
the exact set-theoretic content of good-model descent. -/
theorem quotient_internal_sandwich {X Y Z : Type*} [TopologicalSpace Z]
    (q : X → Y) (π : X → Z) (π' : Y → Z) (hq : Function.Surjective q)
    (hcomm : ∀ x, π' (q x) = π x) (InternalX : Set X → Prop) (InternalY : Set Y → Prop)
    (himage : ∀ B, InternalX B → InternalY (q '' B)) (V : Set Z)
    (hsandwich : ∀ F U : Set Z, IsCompact F → IsOpen U → F ⊆ U → U ⊆ V →
      ∃ B : Set X, InternalX B ∧ π ⁻¹' F ⊆ B ∧ B ⊆ π ⁻¹' U) :
    ∀ F U : Set Z, IsCompact F → IsOpen U → F ⊆ U → U ⊆ V →
      ∃ B : Set Y, InternalY B ∧ π' ⁻¹' F ⊆ B ∧ B ⊆ π' ⁻¹' U := by
  intro F U hF hU hFU hUV
  obtain ⟨B,hB,hFB,hBU⟩ := hsandwich F U hF hU hFU hUV
  refine ⟨q '' B,himage B hB,?_,?_⟩
  · intro y hy
    obtain ⟨x,rfl⟩ := hq y
    exact ⟨x,hFB (by simpa only [Set.mem_preimage,hcomm] using hy),rfl⟩
  · rintro y ⟨x,hx,rfl⟩
    simpa only [Set.mem_preimage,hcomm] using hBU hx

/-- Small and thick model neighbourhoods survive an actual quotient without
assuming any extra topological property of the quotient source. -/
theorem quotient_model_neighbourhood {X Y Z : Type*}
    (q : X → Y) (π : X → Z) (π' : Y → Z) (hq : Function.Surjective q)
    (hcomm : ∀ x, π' (q x) = π x) (A : Set X) (V : Set Z)
    (hsmall : π ⁻¹' V ⊆ A) (hthick : V ⊆ π '' A) :
    π' ⁻¹' V ⊆ q '' A ∧ V ⊆ π' '' (q '' A) := by
  constructor
  · intro y hy
    obtain ⟨x,rfl⟩ := hq y
    exact ⟨x,hsmall (by simpa only [Set.mem_preimage,hcomm] using hy),rfl⟩
  · intro z hz
    obtain ⟨x,hx,he⟩ := hthick hz
    exact ⟨q x,⟨x,hx,rfl⟩,(hcomm x).trans he⟩

namespace LocalGroupCongruence
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    (C : LocalGroupCongruence L)

/-- The descended local model has exactly the same image of the source
approximate set. In particular its image compactness is preserved. -/
theorem liftHom_compact_image [TopologicalSpace H] (f : LocalGroupHom L M)
    (hf : ∀ a b, C.toSetoid.r a b → f.toFun a = f.toFun b)
    (A : Set G) (hA : IsCompact (f.toFun '' A)) :
    IsCompact ((C.liftHom f hf).toFun '' (C.project '' A)) := by
  rw [C.liftHom_image]
  exact hA
end LocalGroupCongruence
end DirectedCycles
