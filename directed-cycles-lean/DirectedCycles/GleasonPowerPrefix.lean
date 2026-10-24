import DirectedCycles.GleasonMetricBasics

set_option autoImplicit false
namespace DirectedCycles
namespace GleasonMetricData
variable {G : Type*} [Group G] [TopologicalSpace G] (D : GleasonMetricData G)

/-- A power segment that remains uniformly small has a generator whose
size is inversely proportional to the segment length. The escape premise
is derived, rather than assumed, by using its first possible failure. -/
theorem gauge_linear_of_power_prefix (g : G) (N : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hscale : (D.constant+1)*R ≤ 1/D.constant)
    (hp : ∀ k ≤ N, D.gauge (g^k) ≤ R) :
    (N : ℝ)*D.gauge g ≤ D.constant*R := by
  classical
  have hC := D.constant_pos
  have hν := D.gauge_nonneg g
  have hlimit : 0 < 1/D.constant := one_div_pos.mpr hC
  have hesc : ∀ n : ℕ, 0 < n → n ≤ N → (n : ℝ)*D.gauge g ≤ 1/D.constant →
      (n : ℝ)*D.gauge g ≤ D.constant*R := by
    intro n hn hnN hsmall
    have he := D.escape g n hn hsmall
    change (n : ℝ)/D.constant*D.gauge g ≤ D.gauge (g^n) at he
    have he' : ((n : ℝ)*D.gauge g)/D.constant ≤ D.gauge (g^n) := by
      convert he using 1; ring
    have h := (div_le_iff₀ hC).mp he'
    have h' := mul_le_mul_of_nonneg_right (hp n hnN) hC.le
    nlinarith
  by_cases hN : N = 0
  · subst N
    simpa only [Nat.cast_zero,zero_mul] using mul_nonneg hC.le hR
  · have hNpos : 0 < N := by omega
    have hbase : D.gauge g ≤ R := by simpa only [pow_one] using hp 1 hNpos
    have hbaseLimit : D.gauge g ≤ 1/D.constant := by nlinarith
    by_cases hsmall : (N : ℝ)*D.gauge g ≤ 1/D.constant
    · exact hesc N hNpos le_rfl hsmall
    · have hex : ∃ m : ℕ, 1/D.constant < (m : ℝ)*D.gauge g := ⟨N,lt_of_not_ge hsmall⟩
      let m := Nat.find hex
      have hm : 1/D.constant < (m : ℝ)*D.gauge g := Nat.find_spec hex
      have hmN : m ≤ N := Nat.find_min' hex (lt_of_not_ge hsmall)
      have hm2 : 2 ≤ m := by
        by_contra h
        have hm1 : m ≤ 1 := by omega
        have hm1R : (m : ℝ) ≤ 1 := by exact_mod_cast hm1
        nlinarith
      have hprev : ((m-1 : ℕ) : ℝ)*D.gauge g ≤ 1/D.constant :=
        le_of_not_gt (Nat.find_min hex (by omega : m-1 < m))
      have h := hesc (m-1) (by omega) (by omega) hprev
      have hcast : (m : ℝ) = ((m-1 : ℕ) : ℝ)+1 := by exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ m)).symm
      nlinarith
end GleasonMetricData
end DirectedCycles
