module

public import DirectedCycles.FiniteGroupDerivatives

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

noncomputable def finiteConvolution (f k : G → ℝ) : G → ℝ :=
  fun x => ∑ y : G, f y * k (y⁻¹*x)

theorem finiteConvolution_sub_left (f h k : G → ℝ) :
    finiteConvolution (f-h) k = finiteConvolution f k - finiteConvolution h k := by
  ext x
  simp [finiteConvolution, sub_mul, Finset.sum_sub_distrib]

theorem finiteConvolution_leftShift (g : G) (f k : G → ℝ) :
    finiteConvolution (leftShift g f) k = leftShift g (finiteConvolution f k) := by
  ext x
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro y
  simp [leftShift, mul_assoc]

theorem groupDerivative_finiteConvolution (g : G) (f k : G → ℝ) :
    groupDerivative g (finiteConvolution f k) = finiteConvolution (groupDerivative g f) k := by
  simp only [groupDerivative, finiteConvolution_sub_left, finiteConvolution_leftShift]

/-- Moving a left translation through the second convolution factor conjugates
its translating element; the order is recorded explicitly. -/
theorem groupDerivative_finiteConvolution_right (h : G) (f k : G → ℝ) (x : G) :
    groupDerivative h (finiteConvolution f k) x =
      ∑ y : G, f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x) := by
  simp only [groupDerivative, leftShift, Pi.sub_apply, finiteConvolution, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  simp [mul_inv_rev, mul_assoc, mul_sub]

theorem groupDerivative_twice_finiteConvolution (g h : G) (f k : G → ℝ) (x : G) :
    groupDerivative h (groupDerivative g (finiteConvolution f k)) x =
      ∑ y : G, groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x) := by
  rw [groupDerivative_finiteConvolution]
  exact groupDerivative_finiteConvolution_right h _ k x

theorem finiteConvolution_nonneg {f k : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (x : G) : 0 ≤ finiteConvolution f k x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (hf y) (hk _))

theorem finiteConvolution_eq_zero {f k : G → ℝ} {A B : Set G}
    (hf : ∀ x, x ∉ A → f x = 0) (hk : ∀ x, x ∉ B → k x = 0)
    {x : G} (hx : x ∉ A*B) : finiteConvolution f k x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y ∈ A
  · have hy' : y⁻¹*x ∉ B := by
      intro h
      exact hx ⟨y,hy,y⁻¹*x,h,by simp⟩
    rw [hk _ hy', mul_zero]
  · rw [hf _ hy, zero_mul]

theorem finiteConvolution_eq_sum_support {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, y ∉ A → f y = 0) (x : G) :
    finiteConvolution f k x = ∑ y ∈ A, f y*k (y⁻¹*x) := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro y _ hy
  rw [hf _ hy, zero_mul]

theorem finiteConvolution_le_card {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hk : ∀ y, 0 ≤ k y ∧ k y ≤ 1)
    (hfs : ∀ y, y ∉ A → f y = 0) (x : G) :
    finiteConvolution f k x ≤ A.card := by
  rw [finiteConvolution_eq_sum_support A hfs]
  calc
    ∑ y ∈ A, f y*k (y⁻¹*x) ≤ ∑ _y ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y _
      nlinarith [(hf y).1, (hf y).2, (hk (y⁻¹*x)).1, (hk (y⁻¹*x)).2]
    _ = A.card := by simp

/-- The second derivative is bounded using only the actual support of the first
factor and a uniform conjugated derivative bound for the second factor. -/
theorem derivativeNorm_twice_convolution_le {f k : G → ℝ} (g h : G) (B : Finset G)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hfs : ∀ y, y ∉ B → groupDerivative g f y = 0)
    (hdf : derivativeNorm f g ≤ s)
    (hdk : ∀ y ∈ B, derivativeNorm k (y⁻¹*h*y) ≤ r) :
    derivativeNorm (groupDerivative g (finiteConvolution f k)) h ≤ (B.card : ℝ)*s*r := by
  classical
  apply (derivativeNorm_le_iff _ _ (by positivity)).2
  intro x
  rw [groupDerivative_twice_finiteConvolution]
  have he : (∑ y : G, groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x)) =
      ∑ y ∈ B, groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro y _ hy
    rw [hfs _ hy, zero_mul]
  rw [he]
  calc
    |∑ y ∈ B, groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x)| ≤
        ∑ y ∈ B, |groupDerivative g f y * groupDerivative (y⁻¹*h*y) k (y⁻¹*x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ B, s*r := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul]
      exact mul_le_mul ((abs_groupDerivative_le f g y).trans hdf)
        ((abs_groupDerivative_le k (y⁻¹*h*y) _).trans (hdk y hy)) (abs_nonneg _) hs
    _ = (B.card : ℝ)*s*r := by simp; ring
end DirectedCycles
