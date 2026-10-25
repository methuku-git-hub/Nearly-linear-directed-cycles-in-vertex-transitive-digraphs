module

public import DirectedCycles.LocalLargeIndexModels
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- Actual model data used in local Lie induction. This structure records
the specified homomorphism, compact image, small and thick neighbourhood,
and finite internal approximation; it asserts no existence theorem. -/
structure LocalSmoothModelData {ι H : Type*} [TopologicalSpace H]
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (A : ∀ i, Finset (G i)) (Q : LocalGroupAlgebra H) where
  map : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q
  compactSet : Set H
  compact : IsCompact compactSet
  image : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))), map.toFun z ∈ compactSet
  window : Set H
  window_open : IsOpen window
  one_mem : Q.one ∈ window
  small : map.toFun ⁻¹' window ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))
  thick : ∀ y ∈ window, ∃ z, map.toFun z = y
  sandwich : ∀ F O : Set H, IsCompact F → IsOpen O → F ⊆ O → O ⊆ window →
    ∃ B : ∀ i, Finset (G i),
      map.toFun ⁻¹' F ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ∧
      localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))) ⊆ map.toFun ⁻¹' O

namespace LocalSmoothModelData
variable {ι H : Type*} [TopologicalSpace H] {U : Ultrafilter ι} {G : ι → Type*}
    {L : ∀ i, LocalGroupAlgebra (G i)} {A : ∀ i, Finset (G i)} {Q : LocalGroupAlgebra H}
    (M : LocalSmoothModelData U G L A Q)

/-- Every part of a good local model survives restriction to an actual
large set of component indices, including the internal approximation data. -/
noncomputable def restrict (s : Set ι) (hs : s ∈ U) :
    LocalSmoothModelData (localLargeIndexUltrafilter U s hs)
      (fun j => G j.val) (fun j => L j.val) (fun j => A j.val) Q where
  map := M.map.comp (localLargeIndexExtend U s hs G L)
  compactSet := M.compactSet
  compact := M.compact
  image := fun z hz => M.image _ ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)
  window := M.window
  window_open := M.window_open
  one_mem := M.one_mem
  small := by
    intro z hz
    exact (localLargeIndex_extend_mem U s hs G L _ z).1 (M.small hz)
  thick := by
    intro y hy
    obtain ⟨z,hz⟩ := M.thick y hy
    refine ⟨(localLargeIndexRestrict U s hs G L).toFun z,?_⟩
    change M.map.toFun ((localLargeIndexExtend U s hs G L).toFun
      ((localLargeIndexRestrict U s hs G L).toFun z)) = y
    rw [localLargeIndex_extend_restrict]
    exact hz
  sandwich := by
    intro F O hF hO hFO hOM
    obtain ⟨B,hBF,hBO⟩ := M.sandwich F O hF hO hFO hOM
    refine ⟨fun j => B j.val,?_,?_⟩
    · intro z hz
      exact (localLargeIndex_extend_mem U s hs G L _ z).1 (hBF hz)
    · intro z hz
      exact hBO ((localLargeIndex_extend_mem U s hs G L _ z).2 hz)

/-- Shrink the finite source and target neighbourhood while retaining the
same map and inherited internal approximation. -/
def shrink {B : ∀ i, Finset (G i)} (C W : Set H) (hC : IsCompact C)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))), M.map.toFun z ∈ C)
    (hWo : IsOpen W) (hW1 : Q.one ∈ W) (hWM : W ⊆ M.window)
    (hsmall : M.map.toFun ⁻¹' W ⊆ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i)))) :
    LocalSmoothModelData U G L B Q where
  map := M.map
  compactSet := C
  compact := hC
  image := himage
  window := W
  window_open := hWo
  one_mem := hW1
  small := hsmall
  thick := fun y hy => M.thick y (hWM hy)
  sandwich := fun F O hF hO hFO hOW => M.sandwich F O hF hO hFO (hOW.trans hWM)
end LocalSmoothModelData
end DirectedCycles
