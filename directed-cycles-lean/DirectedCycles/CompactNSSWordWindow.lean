module

public import DirectedCycles.CompactKernelCyclicWindow
public import DirectedCycles.CompactPowerTrapping

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- NSS supplies symmetric precompact open windows whose prescribed
closed word powers contain no nontrivial entire cyclic orbit. -/
theorem compact_nss_word_window (hnss : HasNoSmallSubgroups G) (n : ℕ) :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
      ∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^n)) → x = 1 := by
  obtain ⟨B,hB,hB1,hfree⟩ := hnss
  let C := B ∩ B⁻¹
  have hC1 : (1 : G) ∈ C := ⟨hB1,by simpa using hB1⟩
  have hCi : C⁻¹ = C := by
    ext z
    change (z⁻¹ ∈ B ∧ (z⁻¹)⁻¹ ∈ B) ↔ (z ∈ B ∧ z⁻¹ ∈ B)
    simp only [inv_inv,and_comm]
  have hbot : IsCompact ((⊥ : Subgroup G) : Set G) := by
    simp only [Subgroup.coe_bot]
    exact isCompact_singleton
  obtain ⟨U,hU,hbotU,hUi,hUc,hUn⟩ := compact_subgroup_closed_word_window (⊥ : Subgroup G)
    hbot (hB.inter hB.inv) (by intro x hx; rw [Subgroup.mem_bot.mp hx]; exact hC1) n
  refine ⟨U,hU,hbotU (Subgroup.one_mem _),hUi,hUc,?_⟩
  intro x hx
  exact cyclic_identity_of_subgroup_free (hfree.mono Set.inter_subset_left) hCi x
    (fun j => hUn (hx j))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- NSS on a fourth-power closure supplies the compact cyclic control
on the original closure needed by the next finite trapping scale. -/
theorem cyclic_nss_closure_of_fourth {U : Set G} (hU1 : (1 : G) ∈ U)
    (hnss : ∀ x : G, (∀ j : ℕ, x^j ∈ closure (U^4)) → x = 1) :
    ∀ x : G, (∀ j : ℕ, x^j ∈ closure U) → x = 1 := by
  have hU4 : U ⊆ U^4 := by
    simpa only [pow_one] using Set.pow_subset_pow_right hU1 (by omega : 1 ≤ 4)
  intro x hx
  exact hnss x (fun j => closure_mono hU4 (hx j))
end DirectedCycles
