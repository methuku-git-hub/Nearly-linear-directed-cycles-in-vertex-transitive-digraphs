module

public import DirectedCycles.InternalSubgroupTransfer
public import DirectedCycles.InternalSetSandwich

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- An internal subgroup of a generated ambient subgroup, bounded by an
actual finite internal set, gives genuine component subgroups in the original
finite ambient groups. Relative internality is not mistaken for absolute
internality: representatives are first cut down to the bounding set. -/
theorem relative_internal_subgroup_components {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ι) G)) (N : Subgroup H)
    (A : ∀ i, Finset (G i)) (hAH : ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))) ⊆ H)
    (hN : IsInternalFiniteIn u G H (N : Set H))
    (hNA : (N : Set H) ⊆ H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (A i : Set (G i)))) :
    ∃ B : ∀ i, Subgroup (G i), ultraSubgroup (u : Filter ι) G B = N.map H.subtype ∧
      ∀ᶠ i in (u : Filter ι), (B i : Set (G i)) ⊆ (A i : Set (G i)) := by
  obtain ⟨D,hDA,hD⟩ := hN.restrict A hNA
  have hDH : ultraSet (u : Filter ι) G (fun i => (D i : Set (G i))) ⊆ H :=
    (ultraSet_mono (u : Filter ι) G _ _ (Eventually.of_forall hDA)).trans hAH
  have he : (N.map H.subtype : Set _) = ultraSet (u : Filter ι) G (fun i => (D i : Set (G i))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Subgroup.mem_map.mp hx
      have hy' : y ∈ H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (D i : Set (G i))) := hD ▸ hy
      exact hy'
    · intro hx
      let y : H := ⟨x,hDH hx⟩
      have hy : y ∈ N := by
        change y ∈ (N : Set H)
        rw [hD]
        exact hx
      exact Subgroup.mem_map.mpr ⟨y,hy,rfl⟩
  obtain ⟨B,hB,hBD⟩ := subgroup_components_of_internal u G (N.map H.subtype) _ he
  refine ⟨B,hB,?_⟩
  filter_upwards [hBD] with i hi
  rw [hi]
  exact hDA i
end DirectedCycles
