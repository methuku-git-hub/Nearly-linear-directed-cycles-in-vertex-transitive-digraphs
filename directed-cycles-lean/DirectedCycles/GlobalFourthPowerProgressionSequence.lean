module

public import DirectedCycles.GlobalCoarseProgressionSequence
public import DirectedCycles.FiniteSmallNeighbourhoods
public import DirectedCycles.PositiveDensityNatBound

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Pointwise
namespace DirectedCycles

/-- Uniform finite small neighbourhoods sharpen the constructed fixed-power
progression to the fourth power, retaining a uniform cardinal multiplier. -/
theorem global_fourth_power_progression_sequence (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    ∃ r c J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ),
      ∃ P : CosetNilprogression (G i) r c,
        P.carrier ⊆ (A i : Set (G i))^4 ∧ (A i).card ≤ J*Nat.card P.carrier := by
  classical
  obtain ⟨L,δ,hL,hδ,hsmall⟩ := FiniteAlmostPeriods.finite_small_neighbourhoods K hK 20
  choose S hS hdensity hS20 using fun i => hsmall (G i) (A i) (hA i)
  obtain ⟨J₀,hJ₀,hbound⟩ := positive_density_nat_bound δ hδ
  obtain ⟨r,c,J₁,hJ₁,hP⟩ := global_coarse_progression_sequence u hu G S L hL hS
  refine ⟨r,c,J₀*J₁,by nlinarith,?_⟩
  filter_upwards [hP] with i hi
  obtain ⟨P,hPA,hPc⟩ := hi
  refine ⟨P,hPA.trans (hS20 i),?_⟩
  exact (hbound (A i).card (S i).card (hdensity i)).trans
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J₀ hPc)
end DirectedCycles
