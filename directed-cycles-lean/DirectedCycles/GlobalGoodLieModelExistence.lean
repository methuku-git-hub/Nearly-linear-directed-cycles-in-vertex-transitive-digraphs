import DirectedCycles.GleasonMetricLieStructure
import DirectedCycles.GlobalGoodLocallyCompactModel
import DirectedCycles.ConnectedLieQuotientModel

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles
universe u

/-- Actual Lie quotient data exist for every supplied globally locally
compact good model. The compact kernel lies in its specified small window. -/
theorem good_model_exists_lie_quotient {G : Type u} [Group G]
    {T : Set G} {Internal : Set G → Prop}
    (M : InternalLocallyCompactGroupModel G T Internal) :
    Nonempty (LieQuotientData M.carrier M.neighbourhood) :=
  gleason_yamabe_theorem M.carrier M.neighbourhood M.open_neighbourhood M.one_mem_neighbourhood

/-- An actual sequence of finite global approximate groups has a globally
locally compact good model and constructed Lie quotient data. Applying
`connectedLieQuotientModel` gives a connected Lie model with the exact source restrictions and
internal-set predicates; no arbitrary subgroup is asserted to be internal. -/
theorem exists_global_good_lie_quotient (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type u) [∀ i, Group (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
    let H := Subgroup.closure B
    ∃ M : InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H),
      Nonempty (LieQuotientData M.carrier M.neighbourhood) := by
  obtain ⟨M⟩ := exists_global_good_locallyCompact_model u hu G A K hK hA
  exact ⟨M, good_model_exists_lie_quotient M⟩

end DirectedCycles
