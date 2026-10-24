import DirectedCycles.LocalInternalImages
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
namespace DirectedCycles

/-- Compact control of source-model images lets an internal compact/open
sandwich descend through an actual component quotient. The finite quotient
sets are images of the constructed finite source sets. -/
theorem local_internal_quotient_sandwich {ι : Type*} (U : Ultrafilter ι)
    (X Y : ι → Type*) (x₀ : ∀ i, X i) (f : ∀ i, X i → Y i)
    (hf : ∀ i, Function.Surjective (f i))
    {H T : Type*} [TopologicalSpace H] [TopologicalSpace T] [T2Space T]
    (π : LocalUltraproduct (U : Filter ι) X → H)
    (ψ : LocalUltraproduct (U : Filter ι) Y → T) (q : H → T) (hq : Continuous q)
    (hcomm : ∀ x, ψ (localUltraMap (U : Filter ι) X Y f x) = q (π x))
    (C : Set H) (hC : IsCompact C) (hπC : ∀ x, π x ∈ C)
    (hsandwich : ∀ F V : Set H, IsCompact F → IsOpen V → F ⊆ V →
      ∃ B : ∀ i, Finset (X i),
        π ⁻¹' F ⊆ localUltraSet (U : Filter ι) X (fun i => (B i : Set (X i))) ∧
        localUltraSet (U : Filter ι) X (fun i => (B i : Set (X i))) ⊆ π ⁻¹' V) :
    ∀ F V : Set T, IsCompact F → IsOpen V → F ⊆ V →
      ∃ B : ∀ i, Finset (Y i),
        ψ ⁻¹' F ⊆ localUltraSet (U : Filter ι) Y (fun i => (B i : Set (Y i))) ∧
        localUltraSet (U : Filter ι) Y (fun i => (B i : Set (Y i))) ⊆ ψ ⁻¹' V := by
  classical
  intro F V hF hV hFV
  have hcompact : IsCompact (C ∩ q ⁻¹' F) := hC.inter_right (hF.isClosed.preimage hq)
  obtain ⟨A,hAin,hAout⟩ := hsandwich (C ∩ q ⁻¹' F) (q ⁻¹' V) hcompact (hV.preimage hq)
    (fun _ hx => hFV hx.2)
  let B := fun i => (A i).image (f i)
  have he : localUltraMap (U : Filter ι) X Y f '' localUltraSet (U : Filter ι) X (fun i => (A i : Set (X i))) =
      localUltraSet (U : Filter ι) Y (fun i => (B i : Set (Y i))) := by
    simpa only [B,Finset.coe_image] using localUltraMap_image (U : Filter ι) X Y x₀ f (fun i => (A i : Set (X i)))
  refine ⟨B,?_,?_⟩
  · intro y hy
    obtain ⟨x,rfl⟩ := localUltraMap_surjective (U : Filter ι) X Y f hf y
    rw [← he]
    refine ⟨x,hAin ⟨hπC x,?_⟩,rfl⟩
    change q (π x) ∈ F
    rw [← hcomm x]
    exact hy
  · intro y hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    change ψ (localUltraMap (U : Filter ι) X Y f x) ∈ V
    rw [hcomm]
    exact hAout hx
end DirectedCycles
