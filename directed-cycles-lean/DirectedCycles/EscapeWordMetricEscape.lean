module

public import DirectedCycles.EscapeWordMetric
public import DirectedCycles.EscapeNormTrapping

@[expose] public section

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- The constructed word metric has quantitative escape. The proof uses
an actual first exit and the next multiple of the prescribed power, with
its remainder controlled in a smaller symmetric identity window. -/
theorem escapeWordGauge_escape {U : Set G} (hU : IsOpen U)
    (hU1 : (1 : G) ∈ U) (hUc : IsCompact (closure U))
    (hNSS : ∀ x : G, (∀ j : ℕ, x^j ∈ closure U) → x = 1)
    {D : ℝ} (hD : 0 < D)
    (hprod : ∀ l : List G, escapeNorm U l.prod ≤ D*(l.map (escapeNorm U)).sum) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ g : G, ∀ n : ℕ, 0 < n →
      (n : ℝ)*escapeWordGauge U g ≤ a →
        b*(n : ℝ)*escapeWordGauge U g ≤ escapeWordGauge U (g^n) := by
  classical
  obtain ⟨V,hV,hV1,hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds hU1)
  let W := V ∩ V⁻¹
  have hW : IsOpen W := hV.inter hV.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1,by simpa using hV1⟩
  have hWi : ∀ x ∈ W, x⁻¹ ∈ W := by
    intro x hx
    exact ⟨hx.2,Set.inv_mem_inv.mpr hx.1⟩
  have hWW : W*W ⊆ U := (Set.mul_subset_mul Set.inter_subset_left Set.inter_subset_left).trans hVV
  obtain ⟨δ,hδ,hball⟩ := escapeWordGauge_ball_subset hU1 hUc hNSS hD hprod hW hW1
  obtain ⟨C,hC,htrap0⟩ := compact_power_trapping hUc hNSS hW hW1
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ U) → x ∈ W := by
    intro x hx
    apply htrap0 x
    intro j hj
    by_cases hj0 : j = 0
    · simpa only [hj0,pow_zero] using subset_closure hU1
    · exact subset_closure (hx j (by omega) hj)
  let a := min δ 1/2
  let b := 1/(2*(C : ℝ)*D)
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a < δ := by
    have h := min_le_left δ 1
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    have h := min_le_right δ 1
    dsimp [a]
    linarith
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a,b,ha,hb,?_⟩
  intro g n hn hng
  have hν : 0 ≤ escapeWordGauge U g := escapeWordGauge_nonneg hU1 g
  have hsmall : ∀ i ≤ n, g^i ∈ W := by
    intro i hi
    apply hball
    exact (escapeWordGauge_pow_le hU1 g i).trans_lt
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hν).trans_lt (hng.trans_lt haδ))
  by_cases hg : g = 1
  · subst g
    simp only [escapeWordGauge_one hU1,one_pow,mul_zero,le_refl]
  · have hex : ∃ m : ℕ, g^m ∉ U := by
      by_contra h
      have hall : ∀ m : ℕ, g^m ∈ U := by simpa using h
      exact hg (hNSS g (fun m => subset_closure (hall m)))
    let m := Nat.find hex
    have hmexit : g^m ∉ U := Nat.find_spec hex
    have hprev : ∀ i < m, g^i ∈ U := fun i hi => not_not.mp (Nat.find_min hex hi)
    have hm : 0 < m := by
      by_contra h
      have : m = 0 := by omega
      exact hmexit (by simpa [this] using hU1)
    have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmν : (m : ℝ)*escapeWordGauge U g ≤ 1 := by
      have h := escapeWordGauge_le hU1 g
      rw [escapeNorm_eq_inv_of_first_exit hU1 hmexit hprev] at h
      have h' := (le_div_iff₀ hmr).mp h
      nlinarith
    let q : ℕ := m/n+1
    have hq : 0 < q := Nat.zero_lt_succ _
    have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
    have hmq : m < n*q := by
      have hd := Nat.div_add_mod m n
      have hmod := Nat.mod_lt m hn
      dsimp [q]
      nlinarith
    have hqn : n*q ≤ m+n := by
      have hd := Nat.div_mul_le_self m n
      dsimp [q]
      nlinarith
    let i : ℕ := n*q-m
    have hi : i ≤ n := by dsimp [i]; omega
    have hmi : m+i = n*q := by dsimp [i]; omega
    have hqexit : (g^n)^q ∉ W := by
      intro hqW
      apply hmexit
      have h := hWW (Set.mul_mem_mul hqW (hWi (g^i) (hsmall i hi)))
      rw [← pow_mul,← hmi,pow_add,mul_inv_cancel_right] at h
      exact h
    have hfrac : 1/(q : ℝ) ≤ (C : ℝ)*D*escapeWordGauge U (g^n) := by
      have he := inv_le_escapeNorm_of_not_mem hW1 hqexit
      have ht := escapeNorm_le_mul_of_trapping hU1 C hC htrap (g^n)
      have hw := escapeNorm_le_mul_escapeWordGauge hD hprod (g^n)
      exact he.trans (ht.trans ((mul_le_mul_of_nonneg_left hw hCr.le).trans_eq (by ring)))
    have hnν : (n : ℝ)*escapeWordGauge U g ≤ 2/(q : ℝ) := by
      apply (le_div_iff₀ hqr).2
      have hqnR : (n : ℝ)*(q : ℝ) ≤ (m : ℝ)+(n : ℝ) := by exact_mod_cast hqn
      have h := mul_le_mul_of_nonneg_right hqnR hν
      nlinarith [hng.trans ha1]
    have hbound : (n : ℝ)*escapeWordGauge U g ≤
        (2*(C : ℝ)*D)*escapeWordGauge U (g^n) := by
      have h := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 2)
      exact hnν.trans (by convert h using 1 <;> ring)
    have hden : 0 < 2*(C : ℝ)*D := by positivity
    have h := (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)
    simpa only [b,one_div,div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using h
end DirectedCycles
