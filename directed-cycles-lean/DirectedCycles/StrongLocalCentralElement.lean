import DirectedCycles.LocalMinimalEscape
import DirectedCycles.StrongLocalEscapeEstimates
import DirectedCycles.LocalPowerExtension

set_option autoImplicit false
namespace DirectedCycles

/-- A strong finite local NSS group has a least-escape element with a
uniform centralizing escape neighbourhood. The commutator and both products
needed for commutation are actually constructed. -/
theorem strong_local_central_element (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G) (A : Finset G), IsStrongLocalFiniteApproximateGroup L K A →
        L.DivisionClosed → L.Reversible → L.IsNSS (A : Set G) →
        (∃ g ∈ A, g ≠ L.one) →
        ∃ u ∈ A, u ≠ L.one ∧ 0 < L.escapeNorm A u ∧
          (∀ v ∈ A, v ≠ L.one → L.escapeNorm A u ≤ L.escapeNorm A v) ∧
          (∀ x, L.escapeNorm A x < δ → L.Commute x u) ∧
          ∃ N : ℕ, 0 < N ∧ ¬ L.PowerIn (A : Set G) u N ∧
            (∀ n < N, L.PowerIn (A : Set G) u n) ∧ L.escapeNorm A u = 1/(N : ℝ) := by
  let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  let D := 2*(1000 : ℝ)^2*(K : ℝ)^11*P^2
  let δ := 1/(2*(D+1))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hden : 0 < 2*(D+1) := by linarith
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδhalf : δ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hDδ : D*δ < 1 := by
    have he : δ*(2*(D+1)) = 1 := by dsimp [δ]; field_simp
    nlinarith
  refine ⟨δ,hδ,hδhalf,?_⟩
  intro G _ L A hA hd hr hNSS hne
  obtain ⟨u,hu,hu1,hupos,hmin⟩ := L.exists_minimal_escape (LocalGroupAlgebra.DivisionClosed.cancellative L hd hr) A
    hA.approximate.one_mem hNSS hne
  refine ⟨u,hu,hu1,hupos,hmin,?_,L.exists_first_escape hA.approximate.one_mem hupos⟩
  intro x hx
  have hxA : x ∈ (A : Set G) := L.mem_of_escapeNorm_lt_one hA.approximate.one_mem (by linarith)
  have hsub : (A : Set G) ⊆ L.wordPower (A : Set G) 10 := by
    intro y hy
    apply L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts (by omega : 1 ≤ 10) (by omega)
    simpa only [L.wordPower_one] using hy
  obtain ⟨k,hk,hbound⟩ := strong_local_commutator_exists L hd hr hA (hsub hxA) (hsub hu)
  apply L.minimal_escape_commutes hr hA.approximate.one_mem hupos hmin hk hbound
  have hmul := mul_le_mul_of_nonneg_left hx.le hD
  exact hmul.trans_lt hDδ
end DirectedCycles
