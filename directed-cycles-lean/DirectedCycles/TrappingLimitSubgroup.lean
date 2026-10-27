module

public import DirectedCycles.CompactWordLimitSelection
public import DirectedCycles.ClosedWordPowers

@[expose] public section

set_option autoImplicit false
open TopologicalSpace Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- The actual compact closure of a contained finite word window. -/
def closedWordWindow {U : Set G} (hU : IsCompact (closure U))
    (Q : Set G) (r : ℕ) (hQr : Q^r ⊆ U) : Compacts G :=
  ⟨closure (Q^r),hU.of_isClosed_subset isClosed_closure (closure_mono hQr)⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem closedWordWindow_coe {U : Set G} (hU : IsCompact (closure U))
    (Q : Set G) (r : ℕ) (hQr : Q^r ⊆ U) :
    (closedWordWindow hU Q r hQr : Set G) = closure (Q^r) := rfl

/-- Finite trapping and compact-set convergence construct a genuine compact
subgroup containing the limiting word window. All small cyclic orbits are
hypotheses about the chosen family; no subgroup trapping input is assumed. -/
theorem trapping_limit_subgroup {ι : Type*} (u : Ultrafilter ι)
    {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U)
    (hUc : IsCompact (closure U)) (Q : ι → Set G) (r : ι → ℕ)
    (hQ1 : ∀ i, (1 : G) ∈ Q i) (hQi : ∀ i, (Q i)⁻¹ = Q i)
    (hr : ∀ i, 0 < r i) (hQr : ∀ i, (Q i)^(r i) ⊆ U)
    (hsmall : ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
      ∀ᶠ i in (u : Filter ι), ∀ q ∈ Q i, ∀ j : ℕ, q^j ∈ V) :
    ∃ E : Compacts G, (1 : G) ∈ E ∧ (E : Set G)⁻¹ = E ∧
      (E : Set G) ⊆ closure U ∧
      Tendsto (fun i => closedWordWindow hUc (Q i) (r i) (hQr i)) (u : Filter ι) (𝓝 E) ∧
      IsCompact (Subgroup.topologicalClosure (Subgroup.closure (E : Set G)) : Set G) ∧
      (Subgroup.topologicalClosure (Subgroup.closure (E : Set G)) : Set G) ⊆ closure (U^4) := by
  let A := fun i => closedWordWindow hUc (Q i) (r i) (hQr i)
  obtain ⟨E,hEU,hlim⟩ := compact_windows_ultrafilter_limit u A hUc
    (Filter.Eventually.of_forall (fun i => closure_mono (hQr i)))
  have hE1 : (1 : G) ∈ E := compact_limit_mem hlim
    (Filter.Eventually.of_forall (fun i => subset_closure (Set.one_mem_pow (hQ1 i))))
  have hEi : (E : Set G)⁻¹ = E := compact_limit_symmetric hlim
    (Filter.Eventually.of_forall (fun i => symmetric_closure_word_power (hQi i) (r i)))
  have hp : ∀ m : ℕ, (E : Set G)^m ⊆ closure (U^4) := by
    intro m
    obtain ⟨V,hV,hV1,_hVi,htrap⟩ := locally_compact_finite_trapping hU hU1 hUi hUc m
    apply compact_limit_power_subset hlim isClosed_closure m
    filter_upwards [hsmall V hV hV1] with i hi
    have hbound := htrap (Q i) (hQ1 i) (hQi i) hi (r i) (hr i) (hQr i)
    change (closure ((Q i)^(r i)))^m ⊆ closure (U^4)
    refine (word_closure_power_subset _ _).trans (closure_mono ?_)
    simpa only [← pow_mul,Nat.mul_comm (r i) m] using hbound
  obtain ⟨hHc,hHU⟩ := compact_subgroup_of_bounded_word_powers hEi
    (compact_closure_word_power hUc 4) hp
  exact ⟨E,hE1,hEi,hEU,hlim,hHc,hHU⟩
end DirectedCycles
