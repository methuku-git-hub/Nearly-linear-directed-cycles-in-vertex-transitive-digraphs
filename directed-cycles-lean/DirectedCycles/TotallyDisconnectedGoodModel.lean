module

public import DirectedCycles.VanDantzig
public import DirectedCycles.InternalGoodModel

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
universe u
variable {G : Type u} [Group G] {T : Set G} {Internal : Set G → Prop}

/-- A totally disconnected good global model supplies an actual internal
subgroup inside the modelled set. The subgroup comes from a compact open
model subgroup and the exact internal sandwich, rather than an assumed
internality of an arbitrary model inverse image. -/
theorem internal_subgroup_of_totallyDisconnected_model
    (M : InternalLocallyCompactGroupModel G T Internal)
    [@TotallyDisconnectedSpace M.carrier M.topology] :
    ∃ N : Subgroup G, Internal (N : Set G) ∧ (N : Set G) ⊆ T ∧
      ∃ F : Finset G, T ⊆ (F : Set G)*(N : Set G) := by
  classical
  obtain ⟨Q,hQo,hQc,hQU⟩ := exists_compact_open_subgroup
    (M.open_neighbourhood.mem_nhds M.one_mem_neighbourhood)
  let N := Q.comap M.map
  obtain ⟨B,hB,hNB,hBN⟩ := M.internal_sandwich (Q : Set M.carrier) (Q : Set M.carrier)
    hQc hQo (Set.Subset.refl _) hQU
  have he : B = (N : Set G) := Set.Subset.antisymm hBN hNB
  have hNT : (N : Set G) ⊆ T := (Set.preimage_mono hQU).trans M.small_neighbourhood
  refine ⟨N,he ▸ hB,hNT,?_⟩
  let U := fun g : G => (fun y : M.carrier => M.map g*y) '' (Q : Set M.carrier)
  have hUo : ∀ g, IsOpen (U g) := fun g => (isOpenMap_mul_left (M.map g)) _ hQo
  have hcover : M.map '' T ⊆ ⋃ g : G, U g := by
    intro y _
    obtain ⟨g,rfl⟩ := M.surjective y
    exact Set.mem_iUnion.mpr ⟨g,⟨1,Q.one_mem,mul_one _⟩⟩
  obtain ⟨F,hF⟩ := M.compact_image.elim_finite_subcover U hUo hcover
  refine ⟨F,?_⟩
  intro x hx
  have hmem := hF (show M.map x ∈ M.map '' T from ⟨x,hx,rfl⟩)
  obtain ⟨g,hg,hy⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨y,hy,he⟩ := hy
  have hn : g⁻¹*x ∈ N := by
    change M.map (g⁻¹*x) ∈ Q
    rw [map_mul,map_inv,← he,inv_mul_cancel_left]
    exact hy
  exact ⟨g,hg,g⁻¹*x,hn,mul_inv_cancel_left g x⟩
end DirectedCycles
