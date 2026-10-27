module

public import DirectedCycles.LocalNormalizedConvolution
public import DirectedCycles.LocalConvolutionDerivativeBound
public import DirectedCycles.LocalDerivativeSupport

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem derivativeNorm_normalizedConvolution_le (hc : L.Cancellative)
    {A : Finset G} {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    {f k : G → ℝ} (hfs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0)
    (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hks : ∀ x, x ∉ L.wordPower (A : Set G) 2 → k x = 0)
    {g : G} (hg : g ∈ A) :
    L.derivativeNorm (L.normalizedConvolution A f k) g ≤ (K : ℝ)*L.derivativeNorm f g := by
  classical
  let R := L.wordPower (A : Set G) 3
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by omega : 3*3 ≤ 200)
  have h23 : L.wordPower (A : Set G) 2 ⊆ R :=
    L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by omega) (by omega)
  have hgR : g ∈ R := by
    have hh := L.wordPower_subset_wordPower hA.one_mem hA.allProducts
      (by omega : 1 ≤ 3) (by omega : 3 ≤ 200)
    apply hh
    rw [L.wordPower_one]
    exact hg
  have hfR : ∀ x, f x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hfs x (fun h => hn (h23 h)))
  have hkR : ∀ x, k x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hks x (fun h => hn (h23 h)))
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)*A.card := by exact_mod_cast (hBcard ▸ local_approximate_doubling hA)
  have hsB : ∀ x, x ∉ B → k x = 0 := by
    intro x hx
    apply hks
    simpa only [B,Set.mem_toFinset] using hx
  have hmass := sum_le_card_support B (fun x => (hk x).2) hsB
  have hd0 := L.derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [L.derivativeNorm_smul,abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹*(L.derivativeNorm f g * ∑ x : G, k x) :=
      mul_le_mul_of_nonneg_left (L.derivativeNorm_convolution_mass_le hc hRdom hgR f k hfR hkR
        (fun x => (hk x).1)) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*(L.derivativeNorm f g * B.card) := by gcongr
    _ ≤ (A.card : ℝ)⁻¹*(L.derivativeNorm f g * ((K : ℝ)*A.card)) := by gcongr
    _ = (K : ℝ)*L.derivativeNorm f g := by field_simp

/-- The local normalized second derivative bound keeps the sharp K squared
factor by proving the third-power support and cubic cardinal estimate. -/
theorem derivativeNorm_twice_normalizedConvolution_le (hc : L.Cancellative)
    {A : Finset G} {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    {f k : G → ℝ} (hfs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0)
    (hks : ∀ x, x ∉ L.wordPower (A : Set G) 2 → k x = 0)
    {g h : G} (hg : g ∈ A) (hh : h ∈ L.wordPower (A : Set G) 3)
    {r : ℝ} (hr : 0 ≤ r)
    (hcomm : ∀ y ∈ L.wordPower (A : Set G) 3, ∃ c ∈ L.wordPower (A : Set G) 3,
      ∃ t, L.mulRel h y t ∧ L.mulRel y c t ∧ L.derivativeNorm k c ≤ r) :
    L.derivativeNorm (L.derivative g (L.normalizedConvolution A f k)) h ≤
      (K : ℝ)^2*L.derivativeNorm f g*r := by
  classical
  let R := L.wordPower (A : Set G) 3
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by omega : 3*3 ≤ 200)
  have h23 : L.wordPower (A : Set G) 2 ⊆ R :=
    L.wordPower_subset_wordPower hA.one_mem hA.allProducts (by omega) (by omega)
  have hgR : g ∈ R := by
    have hv := L.wordPower_subset_wordPower hA.one_mem hA.allProducts
      (by omega : 1 ≤ 3) (by omega : 3 ≤ 200)
    apply hv
    rw [L.wordPower_one]
    exact hg
  have hfR : ∀ x, f x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hfs x (fun h => hn (h23 h)))
  have hkR : ∀ x, k x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hks x (fun h => hn (h23 h)))
  let B := R.toFinset
  have hBR : (B : Set G) ⊆ R := by intro x hx; exact Set.mem_toFinset.mp hx
  have hds : ∀ y, y ∉ B → L.derivative g f y = 0 := by
    intro y hy
    apply L.derivative_support_cube hc hA.one_mem
      (hA.allProducts.mono L (Set.Subset.refl _) (by omega : 3 ≤ 200)) hfs hg
    simpa only [B,Set.mem_toFinset] using hy
  have hBcard : B.card = Nat.card R := by rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)^2*A.card := by
    exact_mod_cast (hBcard ▸ local_approximate_card_cube hA)
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  have hd0 := L.derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [L.derivative_smul,L.derivativeNorm_smul,abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹*((B.card : ℝ)*L.derivativeNorm f g*r) :=
      mul_le_mul_of_nonneg_left (L.derivativeNorm_twice_convolution_le hc hRdom hgR hh f k B hBR hfR hkR
        hd0 hr hds le_rfl (fun y hy => hcomm y (hBR hy))) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*(((K : ℝ)^2*A.card)*L.derivativeNorm f g*r) := by gcongr
    _ = (K : ℝ)^2*L.derivativeNorm f g*r := by field_simp
end LocalGroupAlgebra
end DirectedCycles
