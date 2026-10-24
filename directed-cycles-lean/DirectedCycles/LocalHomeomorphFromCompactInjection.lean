import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
open Set Filter Topology
open scoped Topology
namespace DirectedCycles

/-- Local injectivity and a neighbourhood-image property at one point suffice
to construct an actual local homeomorphism, using a compact restriction. -/
theorem exists_local_homeomorph_of_compact_injection
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f) (x : X)
    (hinj : ∃ U ∈ 𝓝 x, InjOn f U)
    (himage : ∀ U ∈ 𝓝 x, f '' U ∈ 𝓝 (f x)) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ (e : X → Y) = f := by
  classical
  let : Nonempty X := ⟨x⟩
  obtain ⟨U,hU,hUi⟩ := hinj
  obtain ⟨K,hKn,hKU,hK⟩ := local_compact_nhds hU
  have hKi : InjOn f K := hUi.mono hKU
  have hKin : interior K ∈ 𝓝 x := interior_mem_nhds.mpr hKn
  obtain ⟨W,hWsub,hWopen,hWx⟩ := mem_nhds_iff.mp (himage (interior K) hKin)
  let S := interior K ∩ f ⁻¹' W
  have hS : IsOpen S := isOpen_interior.inter (hWopen.preimage hf)
  have hxS : x ∈ S := ⟨mem_of_mem_nhds hKin,hWx⟩
  have hSK : S ⊆ K := fun _ h => interior_subset h.1
  have hSi : InjOn f S := hKi.mono hSK
  have hSW : f '' S = W := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact hz.2
    · intro y hy
      obtain ⟨z,hz,rfl⟩ := hWsub hy
      exact ⟨z,⟨hz,hy⟩,rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKemb : IsEmbedding (K.domRestrict f) :=
    (hf.comp continuous_subtype_val).isClosedEmbedding (fun a b hab =>
      Subtype.ext (hKi a.property b.property hab)) |>.isEmbedding
  have hSemb : IsEmbedding (S.domRestrict f) := hKemb.comp (IsEmbedding.inclusion hSK)
  have hSopen : IsOpen (range (S.domRestrict f)) := by
    have heq : range (S.domRestrict f) = f '' S := by ext y; simp
    rw [heq,hSW]
    exact hWopen
  let e := hSi.toPartialEquiv f S
  have hc : ContinuousOn e e.source := hf.continuousOn
  have ho : IsOpenMap (e.source.domRestrict e) :=
    (show IsOpenEmbedding (S.domRestrict f) from ⟨hSemb,hSopen⟩).isOpenMap
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e hc ho hS,hxS,rfl⟩

end DirectedCycles
