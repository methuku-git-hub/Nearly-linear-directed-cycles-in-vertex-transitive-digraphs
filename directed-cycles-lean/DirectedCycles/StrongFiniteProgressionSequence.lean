module

public import DirectedCycles.StrongFiniteEnlargedNSSRestoration
public import DirectedCycles.GlobalNSSProgressionSequence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Pointwise
namespace DirectedCycles

/-- Applying the proved NSS induction to the actual finite normal quotients
and restoring their kernels gives dense progressions for every sequence of
strong finite approximate groups. -/
theorem strong_finite_progression_sequence (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (K : ℕ) (hK : 1 ≤ K)
    (hA : ∀ i, IsStrongFiniteApproximateGroup K (A i)) :
    ∃ r c J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ),
      ∃ P : CosetNilprogression (G i) r c,
        P.carrier ⊆ (A i : Set (G i))^5 ∧ (A i).card ≤ J*Nat.card P.carrier := by
  classical
  choose H hH hq hnss hrestore using fun i => strong_finite_enlarged_nss_restoration (hA i)
  let : ∀ i, (H i).Normal := hH
  let QG := fun i => Subgroup.closure (A i : Set (G i)) ⧸ H i
  let : ∀ i, Fintype (QG i) := fun i => Fintype.ofFinite _
  let S : ∀ i, Set (QG i) := fun i => (QuotientGroup.mk' (H i)) ''
    ((Subgroup.closure (A i : Set (G i))).subtype ⁻¹' (A i : Set (G i)))
  let B : ∀ i, Finset (QG i) := fun i => (S i).toFinset
  have hcoe : ∀ i, (B i : Set (QG i)) = S i := fun i => Set.coe_toFinset _
  have hBa : ∀ i, IsApproximateSubgroup (K : ℝ) (B i : Set (QG i)) := by
    intro i
    rw [hcoe]
    exact hq i
  have hBn : ∀ i, ∀ y : QG i, (∀ n : ℕ, y^n ∈ (B i : Set (QG i))^4) → y = 1 := by
    intro i y hy
    apply hnss i y
    simpa only [hcoe] using hy
  obtain ⟨r,c,J,hJ,hP⟩ := global_nss_progression_sequence u hu QG B K
    (by exact_mod_cast hK) hBa hBn
  refine ⟨r,c,J,hJ,?_⟩
  filter_upwards [hP] with i hi
  obtain ⟨P,hPA,hPc⟩ := hi
  have hdensity : Nat.card (S i) ≤ J*Nat.card P.carrier := by
    rw [← hcoe i,Nat.card_coe_set_eq,Set.ncard_coe_finset]
    exact hPc
  obtain ⟨R,hRA,hRc⟩ := hrestore i r c P (by simpa only [hcoe] using hPA) J hdensity
  exact ⟨R,hRA,by simpa only [Nat.card_coe_set_eq,Set.ncard_coe_finset] using hRc⟩
end DirectedCycles
