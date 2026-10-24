import DirectedCycles.TotallyDisconnectedFiniteModel
import DirectedCycles.RankZeroCosetNilprogression

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- The full rank-zero coset-nilprogression conclusion for a totally
disconnected good model, with a uniform size bound on finite components. -/
theorem rank_zero_of_totallyDisconnected_model {ι : Type*}
    (u : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (H : Subgroup (GroupUltraproduct (u : Filter ι) G))
    (hAH : ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))) ⊆ H)
    (T : Set H) (hT : T = H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))))
    (M : InternalLocallyCompactGroupModel H T (IsInternalFiniteIn u G H))
    [@TotallyDisconnectedSpace M.carrier M.topology] :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ i in (u : Filter ι), ∃ P : CosetNilprogression (G i) 0 0,
      P.carrier ⊆ (A i : Set (G i)) ∧ Nat.card (A i : Set (G i)) ≤ k*Nat.card P.carrier := by
  obtain ⟨B,E,k,hE,hcov⟩ := finite_subgroup_covers_of_totallyDisconnected_model u G A H hAH T hT M
  refine ⟨max 1 k,le_max_left _ _,?_⟩
  filter_upwards [hcov] with i hi
  refine ⟨subgroupCosetNilprogression (B i),?_,?_⟩
  · simpa only [subgroupCosetNilprogression_carrier] using hi.1
  · exact (rank_zero_card_bound_of_cover (A i) (E i) (B i) hi.2).trans
      (Nat.mul_le_mul_right _ ((hE i).trans (le_max_right 1 k)))
end DirectedCycles
