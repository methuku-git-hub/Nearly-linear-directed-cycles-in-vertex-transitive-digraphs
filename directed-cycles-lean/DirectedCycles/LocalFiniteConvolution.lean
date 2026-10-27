module

public import DirectedCycles.LocalFiniteTranslations
public import DirectedCycles.FiniteGroupConvolution
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Scalar bounds survive zero-extended local translation. -/
theorem leftShift_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (g x : G) :
    0 ≤ L.leftShift g f x := by
  classical
  unfold leftShift
  split_ifs
  · exact hf _
  · exact le_rfl

theorem leftShift_le_one {f : G → ℝ} (hf : ∀ x, f x ≤ 1) (g x : G) :
    L.leftShift g f x ≤ 1 := by
  classical
  unfold leftShift
  split_ifs
  · exact hf _
  · norm_num

theorem leftShift_sum {I : Type*} (s : Finset I) (g : G) (f : I → G → ℝ) :
    L.leftShift g (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, L.leftShift g (f i) x := by
  classical
  funext x
  by_cases h : ∃ y, L.mulRel g y x
  · simp only [leftShift,dite_eq_left h]
  · simp only [leftShift,dite_eq_right h,Finset.sum_const_zero]

theorem leftShift_const_mul (g : G) (c : ℝ) (f : G → ℝ) :
    L.leftShift g (fun x => c*f x) = fun x => c*L.leftShift g f x := by
  classical
  funext x
  by_cases h : ∃ y, L.mulRel g y x
  · simp only [leftShift,dite_eq_left h]
  · simp only [leftShift,dite_eq_right h,mul_zero]

section Finite
variable [Fintype G]

/-- Finite convolution uses the actual partial product and zero outside its
domain, through the already-defined partial left translations. -/
noncomputable def convolution (f k : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y*L.leftShift y k x

theorem convolution_sub_left (f h k : G → ℝ) :
    L.convolution (f-h) k = L.convolution f k-L.convolution h k := by
  funext x
  simp only [convolution,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem convolution_sub_right (f h k : G → ℝ) :
    L.convolution f (h-k) = L.convolution f h-L.convolution f k := by
  funext x
  simp only [convolution,L.leftShift_sub,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem convolution_nonneg {f k : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x) (x : G) :
    0 ≤ L.convolution f k x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hf y) (L.leftShift_nonneg hk y x)

/-- Support is contained in the actual partially defined set product. -/
theorem convolution_eq_zero (hL : L.Cancellative) {f k : G → ℝ} {A B : Set G}
    (hf : ∀ x, x ∉ A → f x = 0) (hk : ∀ x, x ∉ B → k x = 0)
    {x : G} (hx : x ∉ L.setMul A B) : L.convolution f k x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y ∈ A
  · have hshift : L.leftShift y k x = 0 := by
      by_contra h
      by_cases he : ∃ z, L.mulRel y z x
      · obtain ⟨z,hz⟩ := he
        have hzB : z ∈ B := by
          by_contra hz'
          exact h (by rw [L.leftShift_of_mulRel hL hz,hk z hz'])
        exact hx ⟨y,hy,z,hzB,hz⟩
      · exact h (L.leftShift_of_no_preimage he k)
    rw [hshift,mul_zero]
  · rw [hf y hy,zero_mul]

theorem convolution_eq_sum_support {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, y ∉ A → f y = 0) (x : G) :
    L.convolution f k x = ∑ y ∈ A, f y*L.leftShift y k x := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro y _ hy
  rw [hf y hy,zero_mul]

theorem convolution_le_card {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hk : ∀ y, 0 ≤ k y ∧ k y ≤ 1)
    (hs : ∀ y, y ∉ A → f y = 0) (x : G) :
    L.convolution f k x ≤ A.card := by
  rw [L.convolution_eq_sum_support A hs]
  calc
    ∑ y ∈ A, f y*L.leftShift y k x ≤ ∑ _y ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y _
      have hlo := L.leftShift_nonneg (fun z => (hk z).1) y x
      have hhi := L.leftShift_le_one (fun z => (hk z).2) y x
      nlinarith [(hf y).1,(hf y).2]
    _ = A.card := by simp
end Finite

/-- Agreement with global translation is proved from its actual product. -/
theorem ofGroup_leftShift [Group G] (g : G) (f : G → ℝ) :
    (ofGroup G).leftShift g f = DirectedCycles.leftShift g f := by
  funext x
  change (ofGroup G).leftShift g f x = f (g⁻¹*x)
  exact (ofGroup G).leftShift_of_mulRel (ofGroup_cancellative G)
    (show (ofGroup G).mulRel g (g⁻¹*x) x from mul_inv_cancel_left g x) f

theorem ofGroup_convolution [Group G] [Fintype G] (f k : G → ℝ) :
    (ofGroup G).convolution f k = DirectedCycles.finiteConvolution f k := by
  funext x
  simp only [convolution,ofGroup_leftShift,DirectedCycles.leftShift,finiteConvolution]
end LocalGroupAlgebra
end DirectedCycles
