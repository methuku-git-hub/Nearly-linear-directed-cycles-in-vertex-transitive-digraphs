import DirectedCycles.TrappingExitLimit
import DirectedCycles.SymmetricSmallWindowFilter

set_option autoImplicit false
open Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- In a precompact symmetric identity window, some smaller open window
has all of its entire cyclic orbits generating a subgroup that stays in
the original window. The ultrafilter family is constructed from actual
first exits if the conclusion fails. -/
theorem cyclic_core_trapping_precompact {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUi : U⁻¹ = U) (hUc : IsCompact (closure U)) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      (Subgroup.closure (cyclicWindowCore V) : Set G) ⊆ U := by
  classical
  by_contra hn
  have hfail : ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
      ¬ (Subgroup.closure (cyclicWindowCore V) : Set G) ⊆ U := by
    intro V hV hV1 h
    exact hn ⟨V,hV,hV1,h⟩
  let Good := fun V : Set G => IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧ V ⊆ U
  have hc : ∀ V : Set G, ∃ (Q : Set G) (r : ℕ),
      (1 : G) ∈ Q ∧ Q⁻¹ = Q ∧ 0 < r ∧ Q^r ⊆ U ∧
        (Good V → Q = cyclicWindowCore V ∧ ∀ k : ℕ, Q^k ⊆ U → k ≤ r) := by
    intro V
    by_cases hV : Good V
    · obtain ⟨e⟩ := word_exit_radius_exists (cyclicWindowCore_one hV.2.1)
        (cyclicWindowCore_symmetric hV.2.2.1)
        ((cyclicWindowCore_subset V).trans hV.2.2.2) (hfail V hV.1 hV.2.1)
      exact ⟨cyclicWindowCore V,e.radius,cyclicWindowCore_one hV.2.1,
        cyclicWindowCore_symmetric hV.2.2.1,e.positive,e.inside,fun _ => ⟨rfl,e.maximal⟩⟩
    · refine ⟨{1},1,by simp,by simp,by omega,?_,fun h => (hV h).elim⟩
      simpa using hU1
  choose Q r hQr using hc
  let u := symmetricWindowUltrafilter (G := G)
  have hgood : ∀ᶠ V in (u : Filter (Set G)), Good V := by
    filter_upwards [symmetricWindowUltrafilter_windows (G := G),
      symmetricWindowUltrafilter_small (hU.mem_nhds hU1)] with V hV hVU
    exact ⟨hV.1,hV.2.1,hV.2.2,hVU⟩
  have hsmall : ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
      ∀ᶠ V in (u : Filter (Set G)), ∀ q ∈ Q V, ∀ j : ℕ, q^j ∈ W := by
    intro W hW hW1
    filter_upwards [hgood,symmetricWindowUltrafilter_small (hW.mem_nhds hW1)] with V hV hVW
    intro q hq j
    rw [(hQr V).2.2.2.2 hV |>.1] at hq
    exact hVW (hq j)
  apply no_shrinking_word_exit_family u hU hU1 hUi hUc Q r
    (fun V => (hQr V).1) (fun V => (hQr V).2.1) (fun V => (hQr V).2.2.1)
    (fun V => (hQr V).2.2.2.1) hsmall
  · filter_upwards [hgood] with V hV
    rw [(hQr V).2.2.2.2 hV |>.1]
    exact hfail V hV.1 hV.2.1
  · exact hgood.mono (fun V hV => ((hQr V).2.2.2.2 hV).2)
end DirectedCycles
