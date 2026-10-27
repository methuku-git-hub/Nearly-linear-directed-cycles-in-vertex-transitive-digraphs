module

public import DirectedCycles.LocalTaylorEstimate
public import DirectedCycles.LocalUltraproductEscape

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem derivativeNorm_le_of_power_segment (hc : L.Cancellative) {R S : Set G}
    (hdom : L.AllProductsDefined R 3) (hSR : S ⊆ R) {g : G} (hg : g ∈ R)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R)
    {B : ℝ} (hsecond : ∀ h ∈ S, L.derivativeNorm (L.derivative g f) h ≤ B)
    {n : ℕ} (hn : 0 < n) (hp : ∀ i ≤ n, L.PowerIn S g i) :
    L.derivativeNorm f g ≤ 2*‖f‖/(n : ℝ)+B := by
  let p := L.powerSegmentOfPowerIn hp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (L.derivativeNorm_taylor_bound hc hdom p
    (fun i hi => hSR (L.powerSegmentOfPowerIn_mem hp hi)) hg f hf le_rfl hn).trans
  have hsum : (∑ i ∈ Finset.range n, L.derivativeNorm (L.derivative g f) (p.power i)) ≤ (n : ℝ)*B := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, B := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsecond _ (L.powerSegmentOfPowerIn_mem hp (by have := Finset.mem_range.mp hi; omega))
      _ = (n : ℝ)*B := by simp
  calc
    (2*‖f‖+∑ i ∈ Finset.range n, L.derivativeNorm (L.derivative g f) (p.power i))/(n : ℝ) ≤
        (2*‖f‖+(n : ℝ)*B)/(n : ℝ) := div_le_div_of_nonneg_right (add_le_add le_rfl hsum) hnR.le
    _ = 2*‖f‖/(n : ℝ)+B := by field_simp

/-- The local second-derivative estimate controls the first derivative by the
actual escape norm, including zero escape. Every Taylor argument uses a finite
power segment within the explicitly given ambient domain. -/
theorem derivativeNorm_le_escape_of_second (hc : L.Cancellative) {R S : Set G}
    (hdom : L.AllProductsDefined R 3) (hSR : S ⊆ R) {g : G} (hg : g ∈ R)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R)
    (hS : L.one ∈ S) {B : ℝ} (hB : 0 ≤ B)
    (hsecond : ∀ h ∈ S, L.derivativeNorm (L.derivative g f) h ≤ B) :
    L.derivativeNorm f g ≤ 4*‖f‖*L.escapeNorm S g+B := by
  classical
  by_cases hex : ∃ n : ℕ, ¬ L.PowerIn S g n
  · let n := Nat.find hex
    have hn : ¬ L.PowerIn S g n := Nat.find_spec hex
    have hp : ∀ i < n, L.PowerIn S g i := fun i hi => not_not.mp (Nat.find_min hex hi)
    have hn0 : 0 < n := by
      by_contra hh
      have he : n = 0 := by omega
      exact hn (he ▸ (L.powerIn_zero S g).2 hS)
    rw [L.escapeNorm_eq_inv_of_first_exit hS hn hp]
    by_cases hn1 : n = 1
    · simp only [hn1,Nat.cast_one,div_one,_root_.mul_one]
      have ht := L.derivativeNorm_le_two_mul f g
      have hh := norm_nonneg f
      linarith
    · have hm0 : 0 < n-1 := by omega
      have hnr : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hmr : 0 < ((n-1 : ℕ) : ℝ) := by exact_mod_cast hm0
      have hnm : (n : ℝ) ≤ 2*((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2*(n-1))
      apply (L.derivativeNorm_le_of_power_segment hc hdom hSR hg f hf hsecond hm0
        (fun i hi => hp i (by omega))).trans
      apply add_le_add _ le_rfl
      rw [mul_one_div]
      apply (div_le_div_iff₀ hmr hnr).2
      have hh := norm_nonneg f
      nlinarith
  · have hall : ∀ n : ℕ, L.PowerIn S g n := by simpa only [not_exists,not_not] using hex
    rw [(L.escapeNorm_eq_zero_iff hS g).2 hall,mul_zero,zero_add]
    by_contra h
    have hδ : 0 < L.derivativeNorm f g-B := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (2*‖f‖/(L.derivativeNorm f g-B))
    have hn0r : 0 < (n : ℝ) := (div_nonneg (by positivity) hδ.le).trans_lt hn
    have hn0 : 0 < n := by exact_mod_cast hn0r
    have ht := L.derivativeNorm_le_of_power_segment hc hdom hSR hg f hf hsecond hn0 (fun i _ => hall i)
    have hprod := (div_lt_iff₀ hδ).mp hn
    have hprod' : (L.derivativeNorm f g-B)*(n : ℝ) ≤ 2*‖f‖ :=
      (le_div_iff₀ hn0r).mp (by linarith : L.derivativeNorm f g-B ≤ 2*‖f‖/(n : ℝ))
    nlinarith
end LocalGroupAlgebra
end DirectedCycles
