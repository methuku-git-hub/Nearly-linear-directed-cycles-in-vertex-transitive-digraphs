module

public import DirectedCycles.FiniteStructuralAlgebra
public import DirectedCycles.CoreQuotientEmbedding
public import DirectedCycles.SchreierBallGrowth

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite consequence of BGT Theorem 1.6 used here. This is an open
proposition, not an assumption installed into the Lean environment. -/
def FiniteApproximateClassification : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ k r c : ℕ, 1 ≤ k ∧
    ∀ (G : Type) [Group G] [Finite G] (A : Set G), IsApproximateSubgroup K A →
      ∃ U H : Subgroup G, H ≤ U ∧
      ∃ (_hH : (H.subgroupOf U).Normal) (_hNil : Group.IsNilpotent (U ⧸ H.subgroupOf U)),
        (H : Set G) ⊆ A^4 ∧
        Nat.card ↥((Quotient.mk'' : G → G ⧸ U) '' A) ≤ k ∧
        Group.rank (U ⧸ H.subgroupOf U) ≤ r ∧
        Group.nilpotencyClass (U ⧸ H.subgroupOf U) ≤ c

/-- A bounded coset covering of a sufficiently long generating ball
bounds the subgroup index. -/
theorem index_le_of_power_coset_bound {G : Type*} [Group G] [Finite G]
    (S : Set G) (h1 : 1 ∈ S) (hgen : Subgroup.closure S = ⊤)
    (U : Subgroup G) (m k : ℕ) (hkm : k ≤ m)
    (hcover : Nat.card ↥((Quotient.mk'' : G → G ⧸ U) '' (S^m)) ≤ k) : U.index ≤ k := by
  by_contra hu
  have hk : k+1 ≤ U.index := by omega
  have hgrow := finite_coset_growth S h1 hgen U (k+1) hk
  simp only [Nat.add_sub_cancel] at hgrow
  have hsub : (Quotient.mk'' : G → G ⧸ U) '' (S^k) ⊆ Quotient.mk'' '' (S^m) :=
    Set.image_mono (Set.pow_subset_pow_right h1 hkm)
  have hcard := Set.ncard_le_ncard hsub
  have hh := hgrow.trans (hcard.trans hcover)
  omega

/-- Finite BGT Corollary 11.2 and its normality refinement follow from
finite approximate-group classification. Intersecting conjugates of both
subgroups preserves the needed rank bound through an actual product embedding. -/
theorem finite_structure_from_classification (hClass : FiniteApproximateClassification) :
    FiniteApproximateStructure := by
  intro K hK
  obtain ⟨k,r,c,hk,hClass⟩ := hClass K hK
  let R := ∑ i ∈ Finset.range c, ((r+1)^k)^(i+1)
  refine ⟨R,c,k.factorial,k,Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k),hk,?_⟩
  intro G _ _ S h1 _hi hgen m hm happ
  obtain ⟨U,H,hHU,hH,hNil,hHball,hcover,hr,hc⟩ := hClass G (S^m) happ
  let : (H.subgroupOf U).Normal := hH
  let : Group.IsNilpotent (U ⧸ H.subgroupOf U) := hNil
  have hu : U.index ≤ k := index_le_of_power_coset_bound S h1 hgen U m k hm hcover
  have hnorm : U ≤ Subgroup.normalizer H :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHU).mp hH
  obtain ⟨hNilCore,hrCore,hcCore⟩ := normal_core_nilpotent_quotient_bounds U H hnorm r c hr hc
  refine ⟨H.normalCore,U.normalCore,inferInstance,inferInstance,Subgroup.normalCore_mono hHU,
    ?_,hNilCore,?_,hcCore,?_⟩
  · intro g hg
    have hh := hHball (H.normalCore_le hg)
    simpa only [← pow_mul,Nat.mul_comm m 4] using hh
  · exact hrCore.trans (by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega : 1 ≤ r+1) hu) _)
  · exact (finite_normal_core_index U).2.2.trans (Nat.factorial_le hu)

end DirectedCycles
