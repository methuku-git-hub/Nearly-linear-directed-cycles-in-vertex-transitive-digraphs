module

public import DirectedCycles.DenseBinomial
public import DirectedCycles.TruncatedExpansion
public import DirectedCycles.TranslateAveraging

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- The dense-generation multiplier, before choosing the grid side length.
The coefficients and the target use the actual integral truncated group ring. -/
theorem dense_coordinate_multiplier {G : Type*} [Group G] [Fintype G]
    (D L : ℕ) (hL : 0 < L) {n : ℕ} (u : Fin n → G)
    (hu : Function.Surjective (powerWord u)) (E : Finset G)
    (hsize : n*(D-1)*Fintype.card G < E.card*L) :
    ∃ M : ℕ, 0 < M ∧ M ≤ (D^n).factorial * L^((n+2*n*(D-1))*D^n) ∧
      ∀ x : TruncatedGroupRing G D,
        M • x ∈ AddSubgroup.closure (truncatedElement G D '' (E : Set G)) := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range L)
  have hScard : S.card = L^n := by simp [S]
  obtain ⟨z,hz⟩ := dense_translate_sample E S
    (fun t => powerWord u (fun i => (t i : ℤ)))
  let F := S.filter (fun t => z * powerWord u (fun i => (t i : ℤ)) ∈ E)
  have hF : ∀ t ∈ F, ∀ i, t i < L := by
    intro t ht i
    exact Finset.mem_range.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp ht).1 i)
  have hg : (0 : ℚ≥0) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hl : (0 : ℚ≥0) < L := by exact_mod_cast hL
  have havg : (E.card : ℚ≥0) / Fintype.card G ≤ (F.card : ℚ≥0)/(L : ℚ≥0)^n := by
    apply (div_le_div_iff₀ hg (pow_pos hl n)).mpr
    rw [hScard] at hz
    have hc : E.card * L^n ≤ F.card * Fintype.card G := by
      simpa only [F,Nat.mul_comm] using hz
    exact_mod_cast hc
  have hlarge : ((n*(D-1) : ℕ) : ℚ≥0)/L < (F.card : ℚ≥0)/(L : ℚ≥0)^n := by
    apply lt_of_lt_of_le _ havg
    apply (div_lt_div_iff₀ hl hg).mpr
    exact_mod_cast hsize
  let W := AddSubgroup.closure (truncatedElement G D '' (E : Set G))
  obtain ⟨M,hM,hbound,hcoeff⟩ := dense_binomial_multiplier hL F hF hlarge
    (truncatedCoordinateCoefficient D u z) W (by
      intro t ht
      rw [← truncated_nat_coordinates_expansion]
      exact AddSubgroup.subset_closure
        ⟨z * powerWord u (fun i => (t i : ℤ)),(Finset.mem_filter.mp ht).2,rfl⟩)
  exact ⟨M,hM,hbound,truncated_multiplier_of_coefficients D M u hu z W hcoeff⟩

end DirectedCycles
