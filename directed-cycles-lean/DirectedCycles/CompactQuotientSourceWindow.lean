module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A continuous map out of an open local window admits a compact source
neighbourhood inside any prescribed ambient neighbourhood and mapping into
any prescribed target neighbourhood. -/
theorem compact_quotient_source_window {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] (W : Set X) (hW : IsOpen W) (x₀ : W)
    (q : W → Y) (hq : Continuous q) {U : Set X} (hU : U ∈ nhds x₀.val)
    {V : Set Y} (hV : V ∈ nhds (q x₀)) :
    ∃ C : Set X, IsCompact C ∧ x₀.val ∈ interior C ∧ C ⊆ W ∧ C ⊆ U ∧
      ∀ x : W, x.val ∈ C → q x ∈ V := by
  let O := interior U ∩ Subtype.val '' (q ⁻¹' interior V)
  have hO : IsOpen O := isOpen_interior.inter (hW.isOpenMap_subtype_val _ (isOpen_interior.preimage hq))
  have hxO : x₀.val ∈ O := ⟨mem_interior_iff_mem_nhds.mpr hU,
    ⟨x₀,mem_interior_iff_mem_nhds.mpr hV,rfl⟩⟩
  obtain ⟨C,hC,hC₀,hCO⟩ := exists_compact_subset hO hxO
  refine ⟨C,hC,hC₀,?_,fun _ hx => interior_subset (hCO hx).1,?_⟩
  · intro x hx
    obtain ⟨y,_,rfl⟩ := (hCO hx).2
    exact y.property
  · intro x hx
    obtain ⟨y,hy,he⟩ := (hCO hx).2
    have he' : y = x := Subtype.ext he
    rw [← he']
    exact interior_subset hy
end DirectedCycles
