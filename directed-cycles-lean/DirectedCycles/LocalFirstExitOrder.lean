import DirectedCycles.LocalPowerSegment
import DirectedCycles.LocalEscapeNSS
import DirectedCycles.LocalDivision
import DirectedCycles.NestedTangentScaleBounds

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- First exits from nested sets are ordered, using uniqueness of the
actual finite local powers on the common part of their domains. -/
theorem first_exit_mono {A B : Set G} (hBA : B ⊆ A) {u : G} {N M K J : ℕ}
    (p : L.PowerSegment u M) (q : L.PowerSegment u J)
    (hN : N ≤ M) (hK : K ≤ J)
    (hprev : ∀ n < K, q.power n ∈ B) (hexit : p.power N ∉ A) : K ≤ N := by
  by_contra hh
  have hn : N < K := lt_of_not_ge hh
  have he := (p.product N hN).unique L (q.product N (by omega))
  exact hexit (he.symm ▸ hBA (hprev N hn))

/-- In a finite NSS source window, each nonidentity element has strictly
positive escape. No NSS assertion about a later quotient is used. -/
theorem positive_escape_of_finite_nss [Finite G]
    (hd : L.DivisionClosed) (hr : L.Reversible)
    {A : Set G} (hA : L.one ∈ A) (hNSS : L.IsNSS A) {u : G} (hu : u ≠ L.one) :
    0 < L.escapeNorm A u := by
  have hne : L.escapeNorm A u ≠ 0 := fun he =>
    hu ((L.finite_nss_iff_escapeNorm (hd.cancellative L hr) hA).1 hNSS u he)
  exact lt_of_le_of_ne (L.escapeNorm_nonneg hA u) hne.symm
end LocalGroupAlgebra

/-- A least-escape element has at least as large a first-exit time as
any competitor with positive escape. -/
theorem minimal_escape_first_exit_order {N₀ N₁ : ℕ} (hN₀ : 0 < N₀) (hN₁ : 0 < N₁)
    (hmin : 1/(N₀ : ℝ) ≤ 1/(N₁ : ℝ)) : N₁ ≤ N₀ := by
  have h₀ : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have h₁ : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have h := (div_le_div_iff₀ h₀ h₁).1 hmin
  simpa only [one_mul,Nat.cast_le] using h

/-- Combining the outer minimum with both actual nested-scale estimates
produces the 1.1 bound required by the signed correction. -/
theorem local_nested_minimal_exit_comparison {ι : Type*} (U : Ultrafilter ι)
    (N₀ N₁ K₀ K₁ : ι → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ᶠ i in (U : Filter ι), 0 < N₀ i ∧ 0 < N₁ i)
    (hmin : ∀ᶠ i in (U : Filter ι), 1/(N₀ i : ℝ) ≤ 1/(N₁ i : ℝ))
    (h₀ : ∀ᶠ i in (U : Filter ι), (99/100)*δ < (K₀ i : ℝ)/(N₀ i : ℝ))
    (h₁ : ∀ᶠ i in (U : Filter ι), (K₁ i : ℝ)/(N₁ i : ℝ) < (101/100)*δ) :
    ∀ᶠ i in (U : Filter ι), (K₁ i : ℝ) < (11/10)*(K₀ i : ℝ) := by
  filter_upwards [hpos,hmin,h₀,h₁] with i hpi hmi h₀i h₁i
  apply nested_escape_scale_comparison hδ (by exact_mod_cast hpi.1)
    (by exact_mod_cast hpi.2) _ h₀i h₁i
  exact_mod_cast minimal_escape_first_exit_order hpi.1 hpi.2 hmi
end DirectedCycles
