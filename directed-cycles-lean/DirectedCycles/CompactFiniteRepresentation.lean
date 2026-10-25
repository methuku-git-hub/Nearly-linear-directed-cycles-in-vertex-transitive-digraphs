module

public import DirectedCycles.CompactRepresentationAverage
public import DirectedCycles.InvariantSubspaceRepresentation
public import DirectedCycles.CompactNSSFromSeparatingHoms

@[expose] public section

set_option autoImplicit false
open MeasureTheory
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (R : G →* E →L[ℝ] E)
    (hc : ∀ v, Continuous (fun g => R g v))
    (hinner : ∀ g u v, inner ℝ (R g u) (R g v) = inner ℝ u v)

include μ hc hinner

/-- Every moved vector of a strongly continuous orthogonal compact-group
action is detected in an actual finite-dimensional invariant subspace. -/
theorem compact_action_finite_subspace {g : G} {v : E} (hne : R g v ≠ v) :
    ∃ S : Submodule ℝ E, FiniteDimensional ℝ S ∧
      (∀ h w, w ∈ S → R h w ∈ S) ∧ ∃ w ∈ S, R g w ≠ w := by
  let T := rankOneAverage μ (fun h => R h v)
  obtain ⟨a,_,hfin,w,hw,hmove⟩ := compact_spectral_detection T (R g)
    (rankOneAverage_compact μ _ (hc v)) (rankOneAverage_symmetric μ _ (hc v))
    (rankOneAverage_detects μ R hc hne)
  refine ⟨Module.End.eigenspace T.toLinearMap a,hfin,?_,w,hw,hmove⟩
  intro h u hu
  exact commuting_operator_preserves_eigenspace T (R h)
    (rankOneAverage_commutes μ R hc hinner v h).symm a hu

/-- A faithful strongly continuous orthogonal compact-group action gives
arbitrarily small actual compact normal kernels with NSS quotients. -/
theorem compact_nss_of_faithful_hilbert_action
    (hfaithful : ∀ g : G, g ≠ 1 → ∃ v : E, R g v ≠ v) : HasCompactNSSApproximation G := by
  classical
  let J := {S : Submodule ℝ E // FiniteDimensional ℝ S ∧ ∀ g v, v ∈ S → R g v ∈ S}
  let H : J → Type _ := fun S => (S.val →L[ℝ] S.val)ˣ
  let f : ∀ S : J, G →* H S := fun S => invariantSubspaceUnitsRepresentation R S.val S.property.2
  have hf : ∀ S : J, Continuous (f S) := by
    intro S
    let : FiniteDimensional ℝ S.val := S.property.1
    exact invariantSubspaceUnitsRepresentation_continuous R S.val S.property.2 hc
  have hNSS : ∀ S : J, HasNoSmallSubgroups (H S) := by
    intro S
    exact normed_ring_units_nss (A := S.val →L[ℝ] S.val)
  let : ∀ S : J, T1Space (H S) := fun S =>
    (inferInstance : T1Space (S.val →L[ℝ] S.val)ˣ)
  apply compact_nss_approximation_of_separating_homs H f hf hNSS
  intro g hg
  obtain ⟨v,hv⟩ := hfaithful g hg
  obtain ⟨S,hfin,hS,w,hw,hmove⟩ := compact_action_finite_subspace μ R hc hinner hv
  exact ⟨⟨S,hfin,hS⟩,invariantSubspaceUnitsRepresentation_ne_one R S hS hw hmove⟩
end DirectedCycles
