import DirectedCycles.LocalConvolutionNorm
import DirectedCycles.LocalApproximateCube
import DirectedCycles.FiniteConvolutionBounds

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem derivative_smul (f : G → ℝ) (g : G) (c : ℝ) :
    L.derivative g (c • f) = c • L.derivative g f := by
  have he : L.leftShift g (c • f) = c • L.leftShift g f := L.leftShift_const_mul g c f
  unfold derivative
  rw [he,smul_sub]

section Finite
variable [Fintype G]

theorem derivativeNorm_smul (f : G → ℝ) (g : G) (c : ℝ) :
    L.derivativeNorm (c • f) g = |c| * L.derivativeNorm f g := by
  unfold derivativeNorm
  rw [L.derivative_smul,norm_smul,Real.norm_eq_abs]

noncomputable def normalizedConvolution (A : Finset G) (f k : G → ℝ) : G → ℝ :=
  ((A.card : ℝ)⁻¹) • L.convolution f k

theorem convolution_one_lower (hc : L.Cancellative) (A : Finset G)
    (hi : ∀ a ∈ A, L.inv a ∈ A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (hfA : ∀ x ∈ A, f x = 1) (hkA : ∀ x ∈ A, k x = 1) :
    (A.card : ℝ) ≤ L.convolution f k L.one := by
  classical
  have he : (A.card : ℝ) = ∑ x ∈ A, f x*L.leftShift x k L.one := by
    have ht : ∀ x ∈ A, f x*L.leftShift x k L.one = 1 := by
      intro x hx
      rw [L.leftShift_of_mulRel hc (L.mul_inv x),hfA x hx,hkA _ (hi x hx),_root_.one_mul]
    simp_rw [Finset.sum_congr rfl ht]
    simp
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
  intro x _ _
  exact mul_nonneg (hf x) (L.leftShift_nonneg hk x L.one)

theorem normalizedConvolution_one (hc : L.Cancellative) (A : Finset G)
    (hA : L.one ∈ A) (hi : ∀ a ∈ A, L.inv a ∈ A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x)
    (hfA : ∀ x ∈ A, f x = 1) (hkA : ∀ x ∈ A, k x = 1) :
    1 ≤ L.normalizedConvolution A f k L.one := by
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA⟩
  change 1 ≤ (A.card : ℝ)⁻¹*L.convolution f k L.one
  calc
    1 = (A.card : ℝ)⁻¹*A.card := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (L.convolution_one_lower hc A hi hf hk hfA hkA) (by positivity)

theorem normalizedConvolution_support (hc : L.Cancellative) {A : Finset G}
    (hdom : L.AllProductsDefined (A : Set G) 4) {f k : G → ℝ}
    (hf : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0)
    (hk : ∀ x, x ∉ L.wordPower (A : Set G) 2 → k x = 0)
    {x : G} (hx : x ∉ L.wordPower (A : Set G) 4) :
    L.normalizedConvolution A f k x = 0 := by
  have hx' : x ∉ L.setMul (L.wordPower (A : Set G) 2) (L.wordPower (A : Set G) 2) := by
    simpa only [L.wordPower_add hdom (by omega : 2+2 ≤ 4)] using hx
  change (A.card : ℝ)⁻¹*L.convolution f k x = 0
  rw [L.convolution_eq_zero hc hf hk hx',mul_zero]

theorem norm_convolution_le_card (A : Finset G) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hs : ∀ x, x ∉ A → f x = 0) : ‖L.convolution f k‖ ≤ A.card := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (L.convolution_nonneg (fun x => (hf x).1) (fun x => (hk x).1) x)]
  exact L.convolution_le_card A hf hk hs x

theorem norm_normalizedConvolution_le {A : Finset G} {K : ℕ}
    (hA : IsLocalFiniteApproximateGroup L K A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0) :
    ‖L.normalizedConvolution A f k‖ ≤ K := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)*A.card := by
    exact_mod_cast (hBcard ▸ local_approximate_doubling hA)
  have hsB : ∀ x, x ∉ B → f x = 0 := by
    intro x hx
    apply hs
    simpa only [B,Set.mem_toFinset] using hx
  unfold normalizedConvolution
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  calc
    (A.card : ℝ)⁻¹*‖L.convolution f k‖ ≤ (A.card : ℝ)⁻¹*B.card :=
      mul_le_mul_of_nonneg_left (L.norm_convolution_le_card B hf hk hsB) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*((K : ℝ)*A.card) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = K := by field_simp
end Finite
end LocalGroupAlgebra
end DirectedCycles
