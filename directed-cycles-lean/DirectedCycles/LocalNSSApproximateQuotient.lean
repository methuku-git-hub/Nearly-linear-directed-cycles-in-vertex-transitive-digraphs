import DirectedCycles.LocalZeroEscapeNormal
import DirectedCycles.LocalNormalQuotientCardinality
import DirectedCycles.LocalWordPowerMonotonicity
import DirectedCycles.LocalCongruenceDivision

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Exact finite zero-escape set, with its membership condition retained. -/
noncomputable def localZeroEscapeFinset (A : Finset G) : Finset G := by
  classical
  exact A.filter (fun x => L.escapeNorm A x = 0)

/-- Once the local product estimate and source trapping property are proved,
zero escape gives an actual finite NSS approximate quotient. Its local-group
laws, normality, domain of all required words, unchanged covering parameter,
and fibre-cardinality bound are all consequences, not additional premises. -/
theorem local_nss_approximate_quotient
    (hd : L.DivisionClosed) (hr : L.Reversible) {A B : Finset G} {K : ℕ}
    (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hdom : L.AllProductsDefined (A : Set G) 200)
    (C : ℝ)
    (hprod : ∀ x ∈ A, ∀ y ∈ A, ∀ z, L.mulRel x y z →
      L.escapeNorm A z ≤ C*(L.escapeNorm A x+L.escapeNorm A y))
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      L.PowerIn (L.wordPower (A : Set G) 100) x j) → x ∈ A)
    (hB : IsLocalFiniteApproximateGroup L K B)
    (hsmall : L.wordPower (B : Set G) 200 ⊆ (A : Set G)) :
    let H := {x | L.escapeNorm A x = 0}
    ∃ W : L.NormalSubgroupWindow H (L.setMul H A),
      IsLocalFiniteApproximateGroup (W.congruence hd hr).algebra K (W.finiteImage hd hr B) ∧
      (W.congruence hd hr).algebra.IsNSS Set.univ ∧
      (W.congruence hd hr).algebra.DivisionClosed ∧
      (W.congruence hd hr).algebra.Reversible ∧
      B.card ≤ (W.finiteImage hd hr B).card * (localZeroEscapeFinset L A).card := by
  classical
  dsimp only
  have htrap3 : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      L.PowerIn (L.wordPower (A : Set G) 3) x j) → x ∈ A := by
    intro x hx
    apply htrap
    intro j hj hj'
    obtain ⟨y,hy,hp⟩ := hx j hj hj'
    exact ⟨y,L.wordPower_subset_wordPower hA hdom (by omega : 3 ≤ 100) (by omega) hy,hp⟩
  obtain ⟨W,hNSS⟩ := L.zero_escape_normal_window_nss hd hr hA hi
    (hdom.mono L (Set.Subset.refl _) (by omega : 6 ≤ 200)) C hprod 1000 htrap3
  have hHA : {x | L.escapeNorm (A : Set G) x = 0} ⊆ (A : Set G) := by
    intro x hx
    apply L.mem_of_escapeNorm_lt_one hA
    change L.escapeNorm A x = 0 at hx
    rw [hx]
    norm_num
  have hHR : {x | L.escapeNorm (A : Set G) x = 0} ⊆ (localZeroEscapeFinset L A : Set G) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hHA hx,hx⟩
  have hAS : (A : Set G) ⊆ L.setMul {x | L.escapeNorm (A : Set G) x = 0} A := by
    intro x hx
    exact ⟨L.one,L.escapeNorm_one hA,x,hx,L.one_mul x⟩
  have hBS : ∀ n ≤ 200, L.wordPower (B : Set G) n ⊆ L.setMul {x | L.escapeNorm (A : Set G) x = 0} A :=
    fun n hn => (L.wordPower_subset_of_maximum hB.one_mem hB.allProducts hsmall n hn).trans hAS
  have hBsub : (B : Set G) ⊆ L.setMul {x | L.escapeNorm (A : Set G) x = 0} A := by
    simpa only [L.wordPower_one] using hBS 1 (by omega)
  exact ⟨W,W.finiteImage_approximate hd hr hB hBS,hNSS,
    (W.congruence hd hr).algebra_divisionClosed (hd.restrict L _ W.one_mem W.inv_mem),
    (W.congruence hd hr).algebra_reversible (hr.restrict L _ W.one_mem W.inv_mem),
    W.finiteImage_card_bound hd hr B (localZeroEscapeFinset L A) hBsub hHR⟩
end DirectedCycles
