module

public import DirectedCycles.LocalFactorDistance
public import DirectedCycles.LocalTripleProducts
public import DirectedCycles.LocalFiniteTranslations

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- A factor of distance below the separation radius belongs to A, so the
three-letter A-domain justifies translating that factorization. -/
theorem factorDistance_mul_le_of_small {d : G → ℝ} {A : Finset G}
    (hA : L.one ∈ A) (hdom : L.AllProductsDefined (A : Set G) 3)
    (hmul : ∀ {a b c}, a ∈ A → b ∈ A → L.mulRel a b c → d c ≤ d a+d b)
    {r : ℝ} (hsep : ∀ u, u ∉ A → r ≤ d u)
    {g y x : G} (hg : g ∈ A) (hgy : L.mulRel g y x)
    (hy : L.factorDistance d A hA y < r) :
    L.factorDistance d A hA x ≤ d g+L.factorDistance d A hA y := by
  obtain ⟨u,a,ha,hu,he⟩ := L.exists_factorDistance_eq d A hA y
  have huA : u ∈ A := by
    by_contra hn
    have hb := hsep u hn
    rw [he] at hy
    linarith
  obtain ⟨v,hv⟩ := hdom [g,u] (by simp) (by aesop)
  have hgu := (Product.pair_iff L _ _ _).1 hv
  obtain ⟨z,hva,hgz⟩ := hdom.triple L hg huA ha hgu hu
  have hzx : z = x := L.unique hgz hgy
  rw [hzx] at hva
  exact (L.factorDistance_le hA ha hva).trans (by simpa only [he] using hmul hg huA hgu)

noncomputable def factorBump (d : G → ℝ) (A : Finset G) (hA : L.one ∈ A)
    (r : ℝ) (x : G) : ℝ := max (1-L.factorDistance d A hA x/r) 0

theorem factorBump_nonneg (d : G → ℝ) (A : Finset G) (hA : L.one ∈ A) (r : ℝ) (x : G) :
    0 ≤ L.factorBump d A hA r x := le_max_right _ _

theorem factorBump_le_one {d : G → ℝ} (hd : ∀ x, 0 ≤ d x)
    (A : Finset G) (hA : L.one ∈ A) {r : ℝ} (hr : 0 ≤ r) (x : G) :
    L.factorBump d A hA r x ≤ 1 := by
  apply max_le _ (by norm_num)
  have hh := div_nonneg (L.factorDistance_nonneg hd A hA x) hr
  linarith

theorem factorBump_eq_zero_of_le {d : G → ℝ} {A : Finset G} (hA : L.one ∈ A)
    {r : ℝ} (hr : 0 < r) {x : G} (hx : r ≤ L.factorDistance d A hA x) :
    L.factorBump d A hA r x = 0 := by
  apply max_eq_right
  have hh : 1 ≤ L.factorDistance d A hA x/r := (le_div_iff₀ hr).2 (by simpa using hx)
  linarith

theorem factorBump_sub_le {d : G → ℝ} (hd : ∀ x, 0 ≤ d x)
    {A : Finset G} (hA : L.one ∈ A) (hdom : L.AllProductsDefined (A : Set G) 3)
    (hmul : ∀ {a b c}, a ∈ A → b ∈ A → L.mulRel a b c → d c ≤ d a+d b)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ u, u ∉ A → r ≤ d u)
    {g y x : G} (hm : L.mulRel g y x) :
    L.factorBump d A hA r y-L.factorBump d A hA r x ≤ d g/r := by
  by_cases hg : g ∈ A
  · by_cases hy : L.factorDistance d A hA y < r
    · have ht := L.factorDistance_mul_le_of_small hA hdom hmul hsep hg hm hy
      have ht' := div_le_div_of_nonneg_right ht hr.le
      rw [add_div] at ht'
      have hy' : L.factorDistance d A hA y/r < 1 := (div_lt_one hr).2 hy
      have he : L.factorBump d A hA r y = 1-L.factorDistance d A hA y/r := max_eq_left (by linarith)
      have hx' : 1-L.factorDistance d A hA x/r ≤ L.factorBump d A hA r x := le_max_left _ _
      rw [he]
      linarith
    · rw [L.factorBump_eq_zero_of_le hA hr (le_of_not_gt hy)]
      have hx' := L.factorBump_nonneg d A hA r x
      have hg' := div_nonneg (hd g) hr.le
      linarith
  · have hgy : 1 ≤ d g/r := (le_div_iff₀ hr).2 (by simpa using hsep g hg)
    have hy' := L.factorBump_le_one hd A hA hr.le y
    have hx' := L.factorBump_nonneg d A hA r x
    linarith

/-- A local norm bump with its full zero-extended translation estimate. The
proof checks the inverse-product domain at points with no preimage. -/
theorem exists_factor_bump (hdiv : L.DivisionClosed) (hc : L.Cancellative)
    {d : G → ℝ} (hd : ∀ x, 0 ≤ d x) (hd1 : d L.one = 0)
    (hdi : ∀ x, d (L.inv x) = d x)
    (A : Finset G)
    (hmul : ∀ {a b c}, a ∈ A → b ∈ A → L.mulRel a b c → d c ≤ d a+d b)
    (hA : L.one ∈ A) (hi : ∀ a ∈ A, L.inv a ∈ A)
    (hdom : L.AllProductsDefined (A : Set G) 3)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ u, u ∉ A → r ≤ d u) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧
      (∀ x, x ∉ L.wordPower (A : Set G) 2 → φ x = 0) ∧
      (∀ g x, |L.derivative g φ x| ≤ d g/r) := by
  let φ := L.factorBump d A hA r
  refine ⟨φ,fun x => ⟨L.factorBump_nonneg d A hA r x,L.factorBump_le_one hd A hA hr.le x⟩,?_,?_,?_⟩
  · intro x hx
    simp only [φ,factorBump,L.factorDistance_eq_zero hd hd1 hA hx,zero_div,sub_zero,max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  · intro x hx
    apply L.factorBump_eq_zero_of_le hA hr
    apply L.factorDistance_lower_outside_square hA hsep
    simpa only [L.wordPower_add hdom (by omega : 1+1 ≤ 3),L.wordPower_one] using hx
  · intro g x
    by_cases hex : ∃ y, L.mulRel g y x
    · obtain ⟨y,hy⟩ := hex
      change |L.leftShift g φ x-φ x| ≤ _
      rw [L.leftShift_of_mulRel hc hy,abs_le]
      have hxy := L.factorBump_sub_le hd hA hdom hmul hr hsep hy
      have hyx := L.factorBump_sub_le hd hA hdom hmul hr hsep (hdiv.left hy)
      rw [hdi] at hyx
      constructor <;> dsimp only [φ] <;> linarith
    · change |L.leftShift g φ x-φ x| ≤ _
      rw [L.leftShift_of_no_preimage hex,zero_sub,abs_neg,abs_of_nonneg (L.factorBump_nonneg d A hA r x)]
      by_cases hg : g ∈ A
      · have hx : r ≤ L.factorDistance d A hA x := by
          by_contra hn
          have hxsmall : L.factorDistance d A hA x < r := lt_of_not_ge hn
          obtain ⟨u,a,ha,hua,he⟩ := L.exists_factorDistance_eq d A hA x
          have huA : u ∈ A := by
            by_contra hu
            have hh := hsep u hu
            rw [he] at hxsmall
            linarith
          obtain ⟨v,hv⟩ := hdom [L.inv g,u] (by simp) (by aesop)
          have hgu := (Product.pair_iff L _ _ _).1 hv
          obtain ⟨y,_,hy⟩ := hdom.triple L (hi g hg) huA ha hgu hua
          apply hex
          exact ⟨y,by simpa only [L.inv_inv] using hdiv.left hy⟩
        change L.factorBump d A hA r x ≤ _
        rw [L.factorBump_eq_zero_of_le hA hr hx]
        exact div_nonneg (hd g) hr.le
      · have hh : 1 ≤ d g/r := (le_div_iff₀ hr).2 (by simpa using hsep g hg)
        exact (L.factorBump_le_one hd A hA hr.le x).trans hh
end LocalGroupAlgebra
end DirectedCycles
