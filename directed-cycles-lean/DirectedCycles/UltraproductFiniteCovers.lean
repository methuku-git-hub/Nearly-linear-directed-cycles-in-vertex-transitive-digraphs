module

public import DirectedCycles.DensePowerTranslateCover
public import DirectedCycles.UltraproductApproximateGroups

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- Uniform finite translate covers pass to genuine finite covers inside
the ultraproduct. Every representative remains in the required power. -/
theorem ultra_finite_power_cover {ι : Type*} (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    (A R : ∀ i, Finset (G i)) (K d : ℝ) (p : ℕ)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) (hd : 0 < d)
    (hRshort : ∀ i, R i ⊆ A i^16) (hRd : ∀ i, d*(A i).card ≤ (R i).card)
    (hRone : ∀ i, 1 ∈ R i) (hRi : ∀ i, (R i)⁻¹ = R i) :
    ∃ F : Finset (GroupUltraproduct (u : Filter ι) G),
      (F : Set _) ⊆ (ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))))^p ∧
      (ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))))^p ⊆
        (F : Set _)*(ultraSet (u : Filter ι) G (fun i => (R i : Set (G i))))^4 := by
  classical
  let N := ⌈K^(p+15)/d⌉₊
  have hex : ∀ i, ∃ F : Finset (G i), F ⊆ A i^p ∧ F.card ≤ N ∧ A i^p ⊆ F*R i^2 := by
    intro i
    exact FiniteAlmostPeriods.dense_power_translate_cover (A i) (R i) K d p
      (hA i) hd (hRshort i) (hRd i) (hRi i)
  choose F hFA hFc hcov using hex
  have htuple : ∀ i, ∃ a : Fin N → G i, (F i : Set (G i)) ⊆ Set.range a ∧
      ∀ j, a j ∈ (A i : Set (G i))^p := by
    intro i
    apply FiniteAlmostPeriods.bounded_cover_tuple (F i) N (hFc i) _
    · exact_mod_cast hFA i
    · exact Set.one_mem_pow (hA i).one_mem
  choose a hFa ha using htuple
  let c := fun j : Fin N => ultraMk (u : Filter ι) G (fun i => a i j)
  let E := Finset.univ.image c
  have hE : (E : Set _) = Set.range c := by simp [E]
  refine ⟨E,?_,?_⟩
  · rw [hE,← ultraSet_pow]
    rintro z ⟨j,rfl⟩
    exact (ultraMk_mem_ultraSet_iff _ G _ _).mpr (Eventually.of_forall (fun i => ha i j))
  · have hpoint : ∀ i, (A i : Set (G i))^p ⊆ Set.range (a i)*(R i : Set (G i))^4 := by
      intro i
      have hh : (A i : Set (G i))^p ⊆ (F i : Set (G i))*(R i : Set (G i))^2 := by
        exact_mod_cast hcov i
      exact hh.trans (Set.mul_subset_mul (hFa i) (Set.pow_subset_pow_right (hRone i) (by omega : 2 ≤ 4)))
    have hh := ultraSet_mono (u : Filter ι) G _ _ (Eventually.of_forall hpoint)
    rw [ultraSet_pow,ultraSet_mul,ultraSet_pow,ultraSet_finite_range] at hh
    simpa only [hE,c] using hh

end DirectedCycles
