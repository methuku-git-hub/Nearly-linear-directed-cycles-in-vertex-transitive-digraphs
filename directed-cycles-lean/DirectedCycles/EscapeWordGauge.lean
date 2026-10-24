import DirectedCycles.RegularizedEscapeDistance
import DirectedCycles.EscapeSublevelPowers
import DirectedCycles.CompactConjugateWordWindow
import DirectedCycles.CompactPowerTrapping
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
open Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The actual unregularized word gauge associated with escape. -/
noncomputable def escapeWordGauge (U : Set G) : G → ℝ := wordNorm (escapeNorm U)

theorem escapeWordGauge_nonneg {U : Set G} (hU : (1 : G) ∈ U) (g : G) :
    0 ≤ escapeWordGauge U g := wordNorm_nonneg (escapeNorm_nonneg hU) g

theorem escapeWordGauge_one {U : Set G} (hU : (1 : G) ∈ U) : escapeWordGauge U (1 : G) = 0 :=
  wordNorm_one (escapeNorm_nonneg hU)

theorem escapeWordGauge_le {U : Set G} (hU : (1 : G) ∈ U) (g : G) :
    escapeWordGauge U g ≤ escapeNorm U g := wordNorm_le_weight (escapeNorm_nonneg hU) g

theorem escapeWordGauge_mul_le {U : Set G} (hU : (1 : G) ∈ U) (g h : G) :
    escapeWordGauge U (g*h) ≤ escapeWordGauge U g+escapeWordGauge U h :=
  wordNorm_mul_le (escapeNorm_nonneg hU) g h

theorem escapeWordGauge_inv {U : Set G} (hUi : U⁻¹ = U) (g : G) :
    escapeWordGauge U g⁻¹ = escapeWordGauge U g := wordNorm_inv (escapeNorm_inv hUi) g

theorem escapeWordGauge_pow_le {U : Set G} (hU : (1 : G) ∈ U) (g : G) (n : ℕ) :
    escapeWordGauge U (g^n) ≤ (n : ℝ)*escapeWordGauge U g := by
  induction n with
  | zero => simp [escapeWordGauge_one hU]
  | succ n ih =>
      rw [pow_succ]
      exact (escapeWordGauge_mul_le hU _ _).trans ((add_le_add ih le_rfl).trans_eq (by push_cast; ring))

/-- The full product inequality controls escape by its actual word infimum. -/
theorem escapeNorm_le_mul_escapeWordGauge {U : Set G} {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) (g : G) :
    escapeNorm U g ≤ D*escapeWordGauge U g := by
  rw [mul_comm D]
  apply (div_le_iff₀ hD).mp
  apply le_csInf (wordCosts_nonempty (escapeNorm U) g)
  rintro _ ⟨l,hl,rfl⟩
  exact (div_le_iff₀ hD).mpr (by simpa only [hl,mul_comm] using hprod l)

theorem escapeWordGauge_eq_zero_imp {U : Set G} (hU1 : (1 : G) ∈ U)
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ U) → x = 1) {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum)
    {g : G} (hg : escapeWordGauge U g = 0) : g = 1 := by
  have he : escapeNorm U g = 0 := le_antisymm
    (by simpa only [hg,mul_zero] using escapeNorm_le_mul_escapeWordGauge hD hprod g)
    (escapeNorm_nonneg hU1 g)
  exact hNSS g ((escapeNorm_eq_zero_iff hU1 g).mp he)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every positive gauge ball contains an identity neighbourhood. -/
theorem escapeWordGauge_ball_mem_nhds {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U)
    {ε : ℝ} (hε : 0 < ε) : {g | escapeWordGauge U g < ε} ∈ 𝓝 (1 : G) := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  obtain ⟨W,hW,hW1,hWN⟩ := open_identity_word_window hU hU1 N
  apply Filter.mem_of_superset (hW.mem_nhds hW1)
  intro g hg
  apply (escapeWordGauge_le hU1 g).trans_lt
  apply (escapeNorm_le_of_powers (n := N) ?_).trans_lt hN
  intro j hj
  exact hWN (Set.pow_subset_pow_right hW1 hj (Set.pow_mem_pow hg))

/-- Compact cyclic control and the product estimate make gauge balls
cofinal among the given identity neighbourhoods. -/
theorem escapeWordGauge_ball_subset [T2Space G] {U : Set G}
    (hU1 : (1 : G) ∈ U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum)
    {V : Set G} (hV : IsOpen V) (hV1 : (1 : G) ∈ V) :
    ∃ ε : ℝ, 0 < ε ∧ {g | escapeWordGauge U g < ε} ⊆ V := by
  obtain ⟨M,_hM,htrap⟩ := compact_power_trapping hUc hNSS hV hV1
  let ε := (1/((M : ℝ)+1))/D
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro g hg
  have he : escapeNorm U g < 1/((M : ℝ)+1) := by
    apply (escapeNorm_le_mul_escapeWordGauge hD hprod g).trans_lt
    have h := mul_lt_mul_of_pos_left hg hD
    simpa only [ε,mul_div_cancel₀ _ hD.ne'] using h
  exact htrap g (fun n hn => subset_closure (powers_mem_of_escapeNorm_small hU1 he n hn))
end DirectedCycles
