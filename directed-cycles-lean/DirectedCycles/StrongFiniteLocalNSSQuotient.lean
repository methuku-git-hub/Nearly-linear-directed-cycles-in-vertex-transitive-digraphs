module

public import DirectedCycles.LocalNSSApproximateQuotient
public import DirectedCycles.FiniteEscapeNeighbourhoods
public import DirectedCycles.StrongEscapeEstimates
public import DirectedCycles.GlobalToLocalApproximate

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Strong finite approximate groups yield uniformly dense actual local NSS
quotients. All analytic estimates and small neighbourhoods are derived from
the strong-group hypothesis. The density loss is the exact zero-escape fibre
bound, and the output retains the domain-sensitive local structure. -/
theorem strong_finite_local_nss_quotient (K : ℕ) (hK : 1 ≤ K) :
    ∃ (J : ℕ) (d : ℝ), 1 ≤ J ∧ 0 < d ∧
      ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (A : Finset G),
      IsStrongFiniteApproximateGroup K A →
      let L := LocalGroupAlgebra.ofGroup G
      let H := {x | L.escapeNorm A x = 0}
      ∃ T : Finset G, IsApproximateSubgroup (J : ℝ) (T : Set G) ∧
        d*A.card ≤ T.card ∧ (T : Set G)^200 ⊆ (A : Set G) ∧
        ∃ W : L.NormalSubgroupWindow H (L.setMul H A),
          IsLocalFiniteApproximateGroup
            (W.congruence (LocalGroupAlgebra.ofGroup_divisionClosed G)
              (LocalGroupAlgebra.ofGroup_reversible G)).algebra (2*J)
            (W.finiteImage (LocalGroupAlgebra.ofGroup_divisionClosed G)
              (LocalGroupAlgebra.ofGroup_reversible G) T) ∧
          (W.congruence (LocalGroupAlgebra.ofGroup_divisionClosed G)
            (LocalGroupAlgebra.ofGroup_reversible G)).algebra.IsNSS Set.univ ∧
          d*A.card ≤ (W.finiteImage (LocalGroupAlgebra.ofGroup_divisionClosed G)
            (LocalGroupAlgebra.ofGroup_reversible G) T).card *
              ((localZeroEscapeFinset L A).card : ℝ) := by
  classical
  obtain ⟨R,d,hR,hd,hsmall⟩ := finite_escape_neighbourhoods (K : ℝ)
    (by exact_mod_cast hK) 1000 200 (1/2) (by norm_num)
  let J := ⌈R⌉₊
  have hRJ : R ≤ (J : ℝ) := Nat.le_ceil R
  have hJ : 1 ≤ J := by exact_mod_cast hR.trans hRJ
  refine ⟨J,d,hJ,hd,?_⟩
  intro G _ _ _ A hA
  dsimp only
  let L := LocalGroupAlgebra.ofGroup G
  have hAi : ∀ x ∈ A, L.inv x ∈ A := by
    intro x hx
    change x⁻¹ ∈ (A : Set G)
    have hh : x⁻¹ ∈ (A : Set G)⁻¹ := Set.inv_mem_inv.mpr hx
    simpa only [hA.approximate.inv_eq_self] using hh
  obtain ⟨S,hSi,hsmallS,hfirst,hsecond⟩ := hA.trapping
  have htrap4 : ∀ x : G, (∀ k : ℕ, 1 ≤ k → k ≤ 1000 → x^k ∈ (A : Set G)^4) → x ∈ A := by
    intro x hx
    apply hfirst
    intro k hk hk'
    exact Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 4 ≤ 100) (hx k hk hk')
  obtain ⟨T,hT,hTd,hTp⟩ := hsmall G A hA.approximate htrap4
  have hTA : (T : Set G)^200 ⊆ (A : Set G) := by
    intro x hx
    apply mem_of_escapeNorm_lt_one hA.approximate.one_mem
    have he : escapeNorm A x ≤ 1/2 := hTp hx
    linarith
  have hTJ := hT.mono hRJ
  have hTlocal := global_to_local_approximate hJ hTJ
  let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
  have hprod : ∀ x ∈ A, ∀ y ∈ A, ∀ z, L.mulRel x y z →
      L.escapeNorm A z ≤ P*(L.escapeNorm A x+L.escapeNorm A y) := by
    intro x _ y _ z hz
    change x*y = z at hz
    have hh := strong_approximate_product_all hA [x,y]
    simpa only [L,LocalGroupAlgebra.ofGroup_escapeNorm_eq,List.prod_cons,List.prod_nil,
      mul_one,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hz] using hh
  have htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      L.PowerIn (L.wordPower (A : Set G) 100) x j) → x ∈ A := by
    intro x hx
    apply hfirst
    intro j hj hj'
    simpa only [L,LocalGroupAlgebra.ofGroup_wordPower,LocalGroupAlgebra.ofGroup_powerIn_iff] using hx j hj hj'
  obtain ⟨W,hQ,hNSS,_,_,hcard⟩ := local_nss_approximate_quotient L
    (LocalGroupAlgebra.ofGroup_divisionClosed G) (LocalGroupAlgebra.ofGroup_reversible G)
    hA.approximate.one_mem hAi (LocalGroupAlgebra.ofGroup_allProductsDefined (A : Set G) 200)
    P hprod htrap hTlocal (by simpa only [L,LocalGroupAlgebra.ofGroup_wordPower] using hTA)
  exact ⟨T,hTJ,hTd,hTA,W,hQ,hNSS,hTd.trans (by exact_mod_cast hcard)⟩
end DirectedCycles
