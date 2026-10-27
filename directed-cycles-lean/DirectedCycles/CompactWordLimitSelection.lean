module

public import DirectedCycles.CompactWordLimits
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

set_option autoImplicit false
open TopologicalSpace Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [TopologicalSpace G]

/-- Compactness of the actual hyperspace supplies a limit of compact
windows uniformly contained in one compact region. -/
theorem compact_windows_ultrafilter_limit {ι : Type*} (u : Ultrafilter ι)
    (A : ι → Compacts G) {K : Set G} (hK : IsCompact K)
    (hA : ∀ᶠ i in (u : Filter ι), (A i : Set G) ⊆ K) :
    ∃ E : Compacts G, (E : Set G) ⊆ K ∧ Tendsto A (u : Filter ι) (𝓝 E) := by
  exact (Compacts.isCompact_subsets_of_isCompact hK).ultrafilter_le_nhds' (u.map A) hA

/-- A convergent choice of points from convergent compact windows
belongs to the limiting window. -/
theorem compact_limit_varying_mem [T2Space G] {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → Compacts G} {E : Compacts G} {x : ι → G} {y : G}
    (hA : Tendsto A l (𝓝 E)) (hx : Tendsto x l (𝓝 y))
    (hmem : ∀ᶠ i in l, x i ∈ A i) : y ∈ E := by
  by_contra hn
  obtain ⟨U,V,hU,hV,hEU,hyV,hUV⟩ := E.isCompact.separation_of_notMem hn
  have hAU : ∀ᶠ i in l, (A i : Set G) ⊆ U :=
    hA.eventually ((Compacts.isOpen_subsets_of_isOpen hU).mem_nhds hEU)
  have hxV : ∀ᶠ i in l, x i ∈ V := hx.eventually (hV.mem_nhds hyV)
  obtain ⟨i,hi,hui,hvi⟩ := (hmem.and (hAU.and hxV)).exists
  exact Set.disjoint_left.mp hUV (hui hi) hvi

/-- Fixed finite powers of a compact window converge with the window. -/
theorem compact_window_power_tendsto [Group G] [IsTopologicalGroup G]
    {ι : Type*} {l : Filter ι} {A : ι → Compacts G} {E : Compacts G}
    (hA : Tendsto A l (𝓝 E)) (n : ℕ) :
    Tendsto (fun i => compactWindowPower (A i) n) l (𝓝 (compactWindowPower E n)) :=
  (compactWindowPower_continuous n).tendsto E |>.comp hA
end DirectedCycles
