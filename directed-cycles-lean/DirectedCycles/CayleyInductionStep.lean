module

public import DirectedCycles.LargePrimeCayley
public import DirectedCycles.BoundedPrimeCayley
public import DirectedCycles.SpanningBoundMonotonicity

@[expose] public section

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- The complete current-class Cayley step, including the fixed-cutoff
spanning invariant, from uniform strengthened lower-class layer estimates. -/
theorem cayley_bound_from_lower_classes (r c n : ℕ) (hcn : c ≤ n)
    (hlower : ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 < b ∧
      ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
        Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
        Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) b eta)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c → CayleySpanningBound G (n+1) b eps := by
  let k := auxiliaryIndexExponent r c n+1
  let T0 := r*(8*(n+1)+4+1)
  let theta : ℝ := eps/(k : ℝ)^T0
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : 0 < (k : ℝ)^T0 := pow_pos (zero_lt_one.trans_le hk1) T0
  have htheta : 0 < theta := div_pos heps hpow
  have hthetaeps : theta ≤ eps := div_le_self heps.le (one_le_pow₀ hk1)
  have herror : theta*(k : ℝ)^T0 = eps := div_mul_cancel₀ eps hpow.ne'
  obtain ⟨b,hb,hbLayers⟩ := hlower (theta/2) (by positivity)
  let alpha := min (b/4) 1
  have ha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have ha1 : alpha ≤ 1 := min_le_right _ _
  have h4a : 4*alpha ≤ b := by have hh := min_le_left (b/4) (1 : ℝ); dsimp only [alpha]; linarith
  have hLayers : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
      Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) (4*alpha) (theta/2) := by
    intro H _ _ _ hr hc
    exact (hbLayers H hr hc).weaken hb.le h4a le_rfl
  obtain ⟨P,hcut⟩ := exists_prime_loss_cutoff alpha (theta/2) ha (by positivity)
  let base := alpha^(r*(P+1))
  have hbbase : 0 < base := pow_pos ha _
  have hbbase1 : base ≤ 1 := pow_le_one₀ ha.le ha1
  have hbase : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → AbovePrimeCutoff H (n+1) →
      CayleySpanningBound H (n+1) base theta := by
    intro H _ _ _ hr hc hp hnt A hA
    let : Nontrivial H := hnt
    obtain ⟨C,hC,hspan⟩ := large_prime_cayley_uniform r c n hcn alpha (theta/2) ha ha1
      (by positivity) P hcut hLayers H hr hc hp A hA
    refine ⟨C,?_,fun _ => hspan⟩
    simpa only [base,show 2*(theta/2)=theta by ring] using hC
  have hLayers' : ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
      Group.rank H ≤ ∑ i ∈ Finset.range c, r^(i+1) →
      Group.nilpotencyClass H ≤ c/2 → LayerCycleLowerBound H (4*alpha) theta := by
    intro H _ _ _ hr hc
    exact ((hLayers H hr hc).weaken (by positivity) le_rfl (by linarith)).to_lower_bound
  let d := (4*alpha)/(4*(auxiliaryIndexConstant r c n : ℝ))
  let M : ℝ := ((8*(n+1)+4)^(c*∑ i ∈ Finset.range c, r^(i+1)) : ℕ)
  have hd : 0 < d := by
    have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
    exact div_pos (by positivity) (by positivity)
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero (c*∑ i ∈ Finset.range c,r^(i+1)) (by omega : 8*(n+1)+4 ≠ 0)))
  let result := budgetConstant base d M k T0
  have hresult : 0 < result := budgetConstant_pos base d M k T0 hbbase hd (zero_lt_one.trans_le hM)
  have hresultle : result ≤ base := budgetConstant_le_base base d M k T0 hbbase hd hM
  refine ⟨result,hresult,?_⟩
  intro G _ _ _ hr hc hnt S hS
  let : Nontrivial G := hnt
  by_cases hp : AbovePrimeCutoff G (n+1)
  · exact ((hbase G hr hc hp).weaken hbbase.le hresultle hthetaeps) hnt S hS
  · have hbudget : primeBudget G (8*(n+1)+4) ≤ T0 := primeBudget_le_rank_bound r _ hr
    obtain ⟨C,hC⟩ := bounded_prime_cayley_density r c n hcn base (4*alpha) theta hbbase hbbase1
      (by positivity) htheta.le hbase hLayers' T0 G hr hc hbudget S hS
    have hdensity : result*(Nat.card G : ℝ)^(-eps) ≤ (C.length : ℝ)/Nat.card G := by
      change result*(Nat.card G : ℝ)^(-(theta*(k : ℝ)^T0)) ≤ _ at hC
      rwa [herror] at hC
    have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
    exact ⟨C,(length_bound_iff_density_bound result (Nat.card G) eps C.length hGpos).mpr hdensity,
      fun hp' => (hp hp').elim⟩

end DirectedCycles
