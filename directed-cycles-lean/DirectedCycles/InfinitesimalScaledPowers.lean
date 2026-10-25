module

public import DirectedCycles.ScaledPowerInterval
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles

/-- A small exponent-to-exit-time ratio controls every fixed power. -/
theorem natAbs_mul_lt_of_ratio (k : ℤ) (N n : ℕ) (hN : 0 < N)
    (h : |(k : ℝ)/(N : ℝ)| < 1/((n : ℝ)+1)) : (k*(n : ℤ)).natAbs < N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : |(k : ℝ)| < (N : ℝ)/((n : ℝ)+1) := by
    rw [abs_div,abs_of_pos hNr] at h
    exact (div_lt_iff₀ hNr).1 h |>.trans_le (by ring_nf; exact le_rfl)
  have he' : |(k : ℝ)| *((n : ℝ)+1) < N := (lt_div_iff₀ (by positivity)).1 he
  have he'' : |(k : ℝ)| *(n : ℝ) < N := by nlinarith [abs_nonneg (k : ℝ)]
  have ha : |((k*(n : ℤ) : ℤ) : ℝ)| < N := by
    simpa only [Int.cast_mul,Int.cast_natCast,abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] using he''
  have hi : |k*(n : ℤ)| < (N : ℤ) := by exact_mod_cast ha
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- A vanishing exponent-to-exit-time ratio has every standard power in the
internal approximate group. This is a proved infinitesimal-kernel statement. -/
theorem infinitesimal_scaled_powers (A : ∀ i, Set (G i)) (u : ∀ i, G i)
    (N : ι → ℕ) (k : ι → ℤ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), |(k i : ℝ)/(N i : ℝ)| < ε) :
    ∀ n : ℕ, (ultraMk (U : Filter ι) G (fun i => (u i)^(k i)))^n ∈ ultraSet (U : Filter ι) G A := by
  intro n
  rw [← map_pow]
  apply (ultraMk_mem_ultraSet_iff _ G A _).2
  filter_upwards [hN,hi,hprev,hsmall (1/((n : ℝ)+1)) (by positivity)] with i hNi hii hpi hsi
  change ((u i)^(k i))^n ∈ A i
  have hab := natAbs_mul_lt_of_ratio (k i) (N i) n hNi hsi
  have hm : (u i)^(k i*(n : ℤ)) ∈ A i := shortPowerProgression_subset hii (u i) (N i) hpi
    ⟨k i*(n : ℤ),hab,rfl⟩
  simpa only [zpow_mul,zpow_natCast] using hm

/-- Every element obtained above is killed by a model whose image region has
no nontrivial complete cyclic power sequence. -/
theorem map_infinitesimal_scaled_power {H : Type*} [Group H]
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ) (k : ι → ℤ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hi : ∀ᶠ i in (U : Filter ι), (A i)⁻¹ = A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), |(k i : ℝ)/(N i : ℝ)| < ε)
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G)) (π : S →* H)
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z : S, z.val ∈ ultraSet (U : Filter ι) G A → π z ∈ V)
    (hk : ultraMk (U : Filter ι) G (fun i => (u i)^(k i)) ∈ S) :
    π ⟨ultraMk (U : Filter ι) G (fun i => (u i)^(k i)),hk⟩ = 1 := by
  apply hNSS
  intro n
  rw [← map_pow]
  apply himage
  exact infinitesimal_scaled_powers U G A u N k hN hi hprev hsmall n
end DirectedCycles
