import DirectedCycles.StrongLocalApproximateGroups
import DirectedCycles.LocalWordEscape

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- BGT's product bound with the undefined-product convention included.
Small total escape cost proves existence of all bracketings; otherwise the
right side is already at least one. -/
theorem strong_local_wordEscape_le (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A) (l : List G) :
    L.wordEscape A l ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (L.escapeNorm A)).sum := by
  let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  have hK : 1 ≤ K := hA.approximate.one_le
  have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hM : 1 ≤ ((1000000*K^3 : ℕ) : ℝ) := by
    have hK0 : 0 < K := by omega
    have hh : 0 < 1000000*K^3 := by positivity
    exact_mod_cast hh
  have hP : 1 ≤ P := by
    have hh : 1 ≤ (K : ℝ)*((1000000*K^3 : ℕ) : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKr) (sub_nonneg.mpr hM)]
    dsimp [P]
    nlinarith
  have hbound : ∀ g, L.escapeNorm A g ≤ P*L.restrictedProductNorm (A : Set G) (L.escapeNorm A) g := by
    by_cases hK2 : 2 ≤ K
    · exact fun g => L.escapeNorm_le_restricted_unregularized (by linarith)
        (fun ε hε => strong_local_regularized L hd hr hA hK2 hε) hA.approximate.one_mem g
    · have hK1 : K = 1 := by omega
      have hH := local_one_approximate_isGlobalSubgroup (hK1 ▸ hA.approximate)
      intro g
      have hbase : L.escapeNorm A g ≤ L.restrictedProductNorm (A : Set G) (L.escapeNorm A) g := by
        simpa only [one_mul] using L.le_mul_restrictedProductNorm (A := (A : Set G))
          (by norm_num : (0 : ℝ) < 1) (L.escapeNorm_one hA.approximate.one_mem)
          (fun _ _ hm => hH.escapeNorm_mul_le hm) (fun _ => by simp) g
      exact hbase.trans (le_mul_of_one_le_left
        (L.restrictedProductNorm_nonneg (L.escapeNorm_nonneg hA.approximate.one_mem) g) hP)
  apply L.wordEscape_le_of_restricted hA.approximate.one_mem _ hP hbound l
  intro a ha b hb
  obtain ⟨c,hc⟩ := hA.approximate.allProducts [a,b] (by simp) (by aesop)
  exact ⟨c,(LocalGroupAlgebra.Product.pair_iff L _ _ _).1 hc⟩
end DirectedCycles
