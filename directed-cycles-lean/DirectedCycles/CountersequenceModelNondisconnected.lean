module

public import DirectedCycles.TotallyDisconnectedRankZero
public import DirectedCycles.GlobalGoodLocallyCompactModel
public import DirectedCycles.CosetModelBounds
public import DirectedCycles.SubgroupEscapeNorm

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- An actual counterexample sequence cannot have a totally disconnected
good model: that case supplies uniformly large rank-zero finite models and
contradicts the growing counterexample bounds. -/
theorem countersequence_good_model_not_totallyDisconnected (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*) [∀ i, Group (G i)]
    [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] (A : ∀ i, Finset (G i))
    (hA1 : ∀ i, (1 : G i) ∈ A i)
    (hfail : ∀ i, ¬ HasCosetNilprogressionModel (A i : Set (G i)) (i+1))
    (M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' B^4) (IsInternalFiniteIn u G H)) :
    ¬ @TotallyDisconnectedSpace M.carrier M.topology := by
  intro hTD
  let := hTD
  let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure B
  have hAH : ultraSet (u : Filter ℕ) G (fun i => ((A i ^ 4 : Finset (G i)) : Set (G i))) ⊆ H := by
    simp only [Finset.coe_pow,ultraSet_pow]
    exact (Set.pow_subset_pow_left (show B ⊆ H from Subgroup.subset_closure)).trans
      (set_power_subset_subgroup H 4)
  have hTeq : H.subtype ⁻¹' B^4 =
      H.subtype ⁻¹' ultraSet (u : Filter ℕ) G (fun i => ((A i ^ 4 : Finset (G i)) : Set (G i))) := by
    simp only [Finset.coe_pow,ultraSet_pow]
    rfl
  obtain ⟨k,hk,hmodel⟩ := rank_zero_of_totallyDisconnected_model u G (fun i => (A i)^4)
    H hAH (H.subtype ⁻¹' B^4) hTeq M
  have hlarge : ∀ᶠ i in (u : Filter ℕ), k ≤ i+1 :=
    (show ∀ᶠ i in (u : Filter ℕ), k ≤ i from hu (Filter.eventually_ge_atTop k)).mono
      fun i hi => by omega
  obtain ⟨i,⟨P,hP,hcard⟩,hki⟩ := (hmodel.and hlarge).exists
  apply hfail i
  refine ⟨0,0,P,Nat.zero_le _,Nat.zero_le _,?_,?_⟩
  · simpa only [Finset.coe_pow] using hP
  · have hsub : (A i : Set (G i)) ⊆ ((A i ^ 4 : Finset (G i)) : Set (G i)) := by
      simpa only [Finset.coe_pow] using Set.subset_pow (hA1 i) (by omega : 4 ≠ 0)
    have hcount := Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    exact (hcount.trans hcard).trans (Nat.mul_le_mul_right _ hki)
end DirectedCycles
