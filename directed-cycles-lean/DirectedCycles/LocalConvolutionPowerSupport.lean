module

public import DirectedCycles.LocalNormalizedDerivativeBounds
public import DirectedCycles.LocalApproximatePowerCard

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem derivative_support_power (hc : L.Cancellative) {A : Set G}
    (hA : L.one ∈ A) {p N : ℕ} (hdom : L.AllProductsDefined A N) (hp : p+2 ≤ N)
    {f : G → ℝ} (hf : ∀ x, x ∉ L.wordPower A 2 → f x = 0)
    {g : G} (hg : g ∈ L.wordPower A p) {x : G} (hx : x ∉ L.wordPower A (p+2)) :
    L.derivative g f x = 0 := by
  have hx2 : x ∉ L.wordPower A 2 := fun h => hx (L.wordPower_subset_wordPower hA hdom (by omega) hp h)
  have hs : x ∉ L.setMul {g} (L.wordPower A 2) := by
    rintro ⟨a,ha,b,hb,hm⟩
    have he : a = g := ha
    apply hx
    rw [L.wordPower_add hdom hp]
    exact ⟨g,hg,b,hb,he ▸ hm⟩
  simp only [derivative,Pi.sub_apply,L.leftShift_support hc hf g hs,hf x hx2,sub_self]

variable [Fintype G]

/-- The second derivative estimate on the ten-letter window. The support is
A to the twelfth power, and all translation and conjugation domains fit in
three factors from A to the 34th power. -/
theorem derivativeNorm_twice_normalizedConvolution_ten_le (hc : L.Cancellative)
    {A : Finset G} {K : ℕ} (hA : IsLocalFiniteApproximateGroup L K A)
    {f k : G → ℝ} (hfs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0)
    (hks : ∀ x, x ∉ L.wordPower (A : Set G) 2 → k x = 0)
    {g h : G} (hg : g ∈ L.wordPower (A : Set G) 10) (hh : h ∈ L.wordPower (A : Set G) 10)
    {r : ℝ} (hr : 0 ≤ r)
    (hcomm : ∀ y ∈ L.wordPower (A : Set G) 12,
      ∃ c ∈ L.wordPower (A : Set G) 34, ∃ t, L.mulRel h y t ∧ L.mulRel y c t ∧ L.derivativeNorm k c ≤ r) :
    L.derivativeNorm (L.derivative g (L.normalizedConvolution A f k)) h ≤
      (K : ℝ)^11*L.derivativeNorm f g*r := by
  classical
  let R := L.wordPower (A : Set G) 34
  have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by omega : 34*3 ≤ 200)
  have hsub : ∀ {m : ℕ}, m ≤ 34 → L.wordPower (A : Set G) m ⊆ R :=
    fun {_} hm => L.wordPower_subset_wordPower hA.one_mem hA.allProducts hm (by omega)
  have hfR : ∀ x, f x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hfs x (fun h => hn (hsub (by omega : 2 ≤ 34) h)))
  have hkR : ∀ x, k x ≠ 0 → x ∈ R := by
    intro x hx
    by_contra hn
    exact hx (hks x (fun h => hn (hsub (by omega : 2 ≤ 34) h)))
  let B := (L.wordPower (A : Set G) 12).toFinset
  have hBR : (B : Set G) ⊆ R := fun _ hx => hsub (by omega : 12 ≤ 34) (Set.mem_toFinset.mp hx)
  have hds : ∀ y, y ∉ B → L.derivative g f y = 0 := by
    intro y hy
    apply L.derivative_support_power hc hA.one_mem hA.allProducts (by omega : 10+2 ≤ 200) hfs hg
    simpa only [B,Set.mem_toFinset] using hy
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 12) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)^11*A.card := by
    exact_mod_cast (hBcard ▸ local_approximate_card_power hA 11 (by omega))
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  have hd0 := L.derivativeNorm_nonneg f g
  unfold normalizedConvolution
  rw [L.derivative_smul,L.derivativeNorm_smul,abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (A.card : ℝ)⁻¹*((B.card : ℝ)*L.derivativeNorm f g*r) :=
      mul_le_mul_of_nonneg_left (L.derivativeNorm_twice_convolution_le hc hRdom
        (hsub (by omega : 10 ≤ 34) hg) (hsub (by omega : 10 ≤ 34) hh) f k B hBR hfR hkR
        hd0 hr hds le_rfl (fun y hy => hcomm y (Set.mem_toFinset.mp hy))) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*(((K : ℝ)^11*A.card)*L.derivativeNorm f g*r) := by gcongr
    _ = (K : ℝ)^11*L.derivativeNorm f g*r := by field_simp
end LocalGroupAlgebra
end DirectedCycles
