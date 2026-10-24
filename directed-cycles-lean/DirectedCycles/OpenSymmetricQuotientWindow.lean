import DirectedCycles.LocalQuotientSeparation

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- An open symmetric quotient window with its sixth power in any prescribed
identity neighbourhood, obtained by three successive square roots. -/
theorem exists_open_symmetric_sixth_subset {V : Set H} (hV : V ∈ 𝓝 (1 : H)) :
    ∃ W : Set H, IsOpen W ∧ (1 : H) ∈ W ∧ W⁻¹ = W ∧ W^6 ⊆ V := by
  obtain ⟨U₁,h1o,h11,h1⟩ := exists_open_nhds_one_mul_subset hV
  obtain ⟨U₂,h2o,h21,h2⟩ := exists_open_nhds_one_mul_subset (h1o.mem_nhds h11)
  obtain ⟨U₃,h3o,h31,h3⟩ := exists_open_nhds_one_mul_subset (h2o.mem_nhds h21)
  let W := U₃ ∩ U₃⁻¹
  have hWo : IsOpen W := h3o.inter (h3o.preimage ContinuousInv.continuous_inv)
  have hW1 : (1 : H) ∈ W := ⟨h31,by simpa using h31⟩
  have hWi : W⁻¹ = W := by
    ext x
    simp only [W,Set.mem_inv,Set.mem_inter_iff,inv_inv]
    exact and_comm
  have h32 : U₃^2 ⊆ U₂ := by simpa only [pow_two] using h3
  have h34 : U₃^4 ⊆ U₁ := by
    have he : U₃^4 = (U₃^2)^2 := by rw [← pow_mul]
    rw [he]
    exact (Set.pow_subset_pow_left h32).trans (by simpa only [pow_two] using h2)
  have h38 : U₃^8 ⊆ V := by
    have he : U₃^8 = (U₃^4)^2 := by rw [← pow_mul]
    rw [he]
    exact (Set.pow_subset_pow_left h34).trans (by simpa only [pow_two] using h1)
  refine ⟨W,hWo,hW1,hWi,?_⟩
  exact (Set.pow_subset_pow_left (show W ⊆ U₃ from Set.inter_subset_left)).trans
    ((Set.pow_subset_pow_right h31 (by omega : 6 ≤ 8)).trans h38)
end DirectedCycles
