import DirectedCycles.GleasonCoordinateRootComparison

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The actual exponential chart is locally bi-Lipschitz for the original
Gleason metric. The quadratic root errors disappear in the subdivision limit. -/
theorem exists_coordinateExp_bilipschitz : ∃ a b s : ℝ, 0 < a ∧ 0 < b ∧ 0 < s ∧
    ∀ x y : E, ‖x‖ ≤ s → ‖y‖ ≤ s →
      a*‖y-x‖ ≤ D.metric.dist (coordinateExp D e x) (coordinateExp D e y) ∧
      D.metric.dist (coordinateExp D e x) (coordinateExp D e y) ≤ b*‖y-x‖ := by
  obtain ⟨A,hA,hspeed⟩ := exists_coordinate_speed D e
  obtain ⟨c,u,hc,hu,hlow⟩ := exists_coordinateExp_lower_bound D e
  obtain ⟨r₀,hr₀,hp₀⟩ := D.exists_power_distance_radius
  have hC := D.constant_pos
  let r := min r₀ (1/(8*D.constant))
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  have hr : r ≤ 1/(8*D.constant) := min_le_right _ _
  have hp : ∀ g h : G, ∀ n : ℕ, 0 < n → (n : ℝ)*D.gauge g ≤ r → (n : ℝ)*D.gauge h ≤ r →
      (n : ℝ)/(2*D.constant)*D.metric.dist g h ≤ D.metric.dist (g^n) (h^n) ∧
      D.metric.dist (g^n) (h^n) ≤ 2*(n : ℝ)*D.metric.dist g h := by
    intro g h n hn hg hh
    exact hp₀ g h n hn (hg.trans (min_le_left _ _)) (hh.trans (min_le_left _ _))
  let s := r/(2*A)
  have hs : 0 < s := div_pos hrpos (by positivity)
  refine ⟨c/(2*D.constant),2*A,s,by positivity,by positivity,hs,?_⟩
  intro x y hx hy
  have hsmall : A*(‖x‖+‖y‖) ≤ r := by
    have heq : 2*A*s = r := by dsimp [s]; field_simp
    nlinarith
  let K := 4*D.constant*A^2*‖x‖*‖y‖
  let d := D.metric.dist (coordinateExp D e x) (coordinateExp D e y)
  have hnorm (n : ℕ) (hn : 0 < n) : ‖(1/(n : ℝ)) • (y-x)‖ = ‖y-x‖/(n : ℝ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hnR)]
    ring
  have hsmalln : ∀ᶠ n : ℕ in atTop, ‖y-x‖/(n : ℝ) ≤ u :=
    ((tendsto_const_div_atTop_nhds_zero_nat ‖y-x‖).eventually (gt_mem_nhds hu)).mono fun _ h => h.le
  have hlowerEv : ∀ᶠ n : ℕ in atTop, c*‖y-x‖ ≤ 2*D.constant*d+K/(n : ℝ) := by
    filter_upwards [hsmalln,eventually_ge_atTop 1] with n hnsmall hn1
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := hlow ((1/(n : ℝ)) • (y-x)) (by rw [hnorm n hn]; exact hnsmall)
    have hm := mul_le_mul_of_nonneg_left hl hnR.le
    rw [hnorm n hn] at hm
    have heq : (n : ℝ)*(c*(‖y-x‖/(n : ℝ))) = c*‖y-x‖ := by field_simp
    rw [heq] at hm
    exact hm.trans (coordinate_root_comparison D e hp hr hA.le hspeed x y hsmall n hn).1
  have hlowerLim : Tendsto (fun n : ℕ => 2*D.constant*d+K/(n : ℝ)) atTop (𝓝 (2*D.constant*d)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat K)
  have hlower : c*‖y-x‖ ≤ 2*D.constant*d :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlowerLim hlowerEv
  have hupperEv : ∀ᶠ n : ℕ in atTop, d ≤ 2*A*‖y-x‖+(2*K)/(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := coordinateExp_gauge_bound D e hspeed ((1/(n : ℝ)) • (y-x))
    rw [hnorm n hn] at hb
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*(n : ℝ) by positivity)
    have heq : 2*(n : ℝ)*(A*(‖y-x‖/(n : ℝ))) = 2*A*‖y-x‖ := by field_simp
    rw [heq] at hm
    exact (coordinate_root_comparison D e hp hr hA.le hspeed x y hsmall n hn).2.trans (add_le_add_left hm _)
  have hupperLim : Tendsto (fun n : ℕ => 2*A*‖y-x‖+(2*K)/(n : ℝ)) atTop (𝓝 (2*A*‖y-x‖)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (2*K))
  have hupper : d ≤ 2*A*‖y-x‖ := le_of_tendsto_of_tendsto tendsto_const_nhds hupperLim hupperEv
  refine ⟨?_,hupper⟩
  have heq : c/(2*D.constant)*‖y-x‖ = (c*‖y-x‖)/(2*D.constant) := by ring
  rw [heq]
  apply (div_le_iff₀ (show 0 < 2*D.constant by positivity)).mpr
  nlinarith

end DirectedCycles.GleasonLieAlgebra
