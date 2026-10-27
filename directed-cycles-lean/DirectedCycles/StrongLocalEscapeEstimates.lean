module

public import DirectedCycles.StrongLocalApproximateGroups
public import DirectedCycles.LocalFiniteGleasonCommutator
public import DirectedCycles.LocalSubgroupWords

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

omit [Fintype G] in
/-- The local strong-group conjugation estimate, with its explicit trapping
constant and actual conjugation product. -/
theorem strong_local_approximate_conjugate (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {y g c : G} (hy : y ∈ L.wordPower (A : Set G) 10)
    (hp : L.Product [L.inv y,g,y] c) :
    L.escapeNorm A c ≤ 1000*L.escapeNorm A g := by
  obtain ⟨S,_,_,_,hfirst,_⟩ := hA.trapping
  exact L.escapeNorm_conjugate_twelve hr hA.approximate.one_mem hA.approximate.inv_mem
    hA.approximate.allProducts 1000 (by omega) hfirst
    (L.wordPower_subset_wordPower hA.approximate.one_mem hA.approximate.allProducts
      (by omega : 10 ≤ 12) (by omega) hy) hp

/-- The commutator estimate for every parameter K, including K = 1.
No analytic estimate remains as an additional premise. -/
theorem strong_local_approximate_commutator (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {g h k : G} (hg : g ∈ L.wordPower (A : Set G) 10) (hh : h ∈ L.wordPower (A : Set G) 10)
    (hk : L.Product [L.inv g,L.inv h,g,h] k) :
    let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
    L.escapeNorm A k ≤ (2*(1000 : ℝ)^2*(K : ℝ)^11*P^2)*L.escapeNorm A g*L.escapeNorm A h := by
  dsimp only
  by_cases hK : 2 ≤ K
  · obtain ⟨S,_,_,_,hfirst,_⟩ := hA.trapping
    have hK0 : 0 < K := by omega
    exact L.finite_gleason_commutator hd hr A hA.approximate 1000 (by omega) hfirst
      (by positivity) (fun ε hε => strong_local_regularized L hd hr hA hK hε) hg hh hk
  · have hK1 : K = 1 := by have := hA.approximate.one_le; omega
    subst K
    have hH := local_one_approximate_isGlobalSubgroup hA.approximate
    have hgA := hH.wordPower_subset 10 hg
    have hhA := hH.wordPower_subset 10 hh
    have hkA := hH.product_mem hk (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact hH.inv_mem g hgA
      · exact hH.inv_mem h hhA
      · exact hgA
      · exact hhA)
    rw [hH.escapeNorm_eq_zero (Set.Subset.refl _) hH.one_mem hkA,
      hH.escapeNorm_eq_zero (Set.Subset.refl _) hH.one_mem hgA]
    simp only [mul_zero,zero_mul,le_refl]

/-- Commutator existence is supplied by the local domain; it is not hidden
in the conditional form of the estimate. -/
theorem strong_local_commutator_exists (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    {g h : G} (hg : g ∈ L.wordPower (A : Set G) 10) (hh : h ∈ L.wordPower (A : Set G) 10) :
    let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
    ∃ k, L.Product [L.inv g,L.inv h,g,h] k ∧
      L.escapeNorm A k ≤ (2*(1000 : ℝ)^2*(K : ℝ)^11*P^2)*L.escapeNorm A g*L.escapeNorm A h := by
  dsimp only
  have hgi := L.inv_mem_wordPower hr hA.approximate.inv_mem hg
  have hhi := L.inv_mem_wordPower hr hA.approximate.inv_mem hh
  obtain ⟨k,hk⟩ := (hA.approximate.allProducts.wordPower L (by omega : 10*4 ≤ 200))
    [L.inv g,L.inv h,g,h] (by simp) (by aesop)
  exact ⟨k,hk,strong_local_approximate_commutator L hd hr hA hg hh hk⟩
end DirectedCycles
