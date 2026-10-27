module

public import DirectedCycles.MinimalEscapeWindow

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A fixed centralizing radius depending only on the commutator constant. -/
noncomputable def centralizingEscapeRadius (D : ℝ) : ℝ := min (1/2) (1/(2*(D+1)))

theorem centralizingEscapeRadius_pos {D : ℝ} (hD : 0 ≤ D) :
    0 < centralizingEscapeRadius D := by
  unfold centralizingEscapeRadius
  exact lt_min (by norm_num) (by positivity)

theorem centralizingEscapeRadius_le_half (D : ℝ) : centralizingEscapeRadius D ≤ 1/2 :=
  min_le_left _ _

/-- The same radius works for every group with the same commutator constant;
there is no component-dependent choice of a neighbourhood. -/
theorem centralizes_of_escapeNorm_le_radius {G : Type*} [Group G]
    {A : Set G} (hA : 1 ∈ A) {u : G} (hu : 0 < escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v)
    {D : ℝ} (hD : 0 ≤ D)
    (hcomm : ∀ x ∈ A, escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u)
    {x : G} (hx : escapeNorm A x ≤ centralizingEscapeRadius D) : Commute x u := by
  have hxA : x ∈ A := mem_of_escapeNorm_lt_one hA (lt_of_le_of_lt
    (hx.trans (centralizingEscapeRadius_le_half D)) (by norm_num))
  apply minimal_escape_commutes hA hu hmin (hcomm x hxA)
  have hden : 0 < 2*(D+1) := by positivity
  have hrad : centralizingEscapeRadius D ≤ 1/(2*(D+1)) := min_le_right _ _
  have hrad' := (le_div_iff₀ hden).1 hrad
  have hDx := mul_le_mul_of_nonneg_left hx hD
  nlinarith

/-- A uniform radius for all first-exit progression quotient windows. -/
noncomputable def centralQuotientRadius (C : ℕ) (B D : ℝ) : ℝ :=
  min ((1/(2*((C : ℝ)+2)))/(6*B)) (centralizingEscapeRadius D)

theorem centralQuotientRadius_pos (C : ℕ) {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D) :
    0 < centralQuotientRadius C B D := by
  apply lt_min (by positivity) (centralizingEscapeRadius_pos hD)

theorem uniform_central_quotient_window {G : Type*} [Group G]
    {A : Set G} (hA : 1 ∈ A) (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D)
    (hprod : ∀ l : List G, escapeNorm A l.prod ≤ B*(l.map (escapeNorm A)).sum)
    {u : G} (hu : 0 < escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v)
    (hcomm : ∀ x ∈ A, escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u)
    {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A) :
    let δ := centralQuotientRadius C B D
    0 < δ ∧ δ ≤ 1/2 ∧ (∀ x ∈ escapeSublevel A δ, Commute x u) ∧
      ∃ V : Set G, LocalNormalSet (shortPowerProgression u N) V ∧
        (escapeSublevel A δ)^6 ⊆ V := by
  let r : ℝ := 1/(2*((C : ℝ)+2))
  let δ := centralQuotientRadius C B D
  have hcentral : ∀ x ∈ escapeSublevel A δ, Commute x u := by
    intro x hx
    exact centralizes_of_escapeNorm_le_radius hA hu hmin hD hcomm
      (le_trans hx (min_le_right _ _))
  have hV : LocalNormalSet (shortPowerProgression u N) (centralEscapeWindow A u r) := by
    apply shortPowerProgression_localNormal hi C htrap u hN hexit hprev
    · intro x hx
      apply powers_mem_of_escapeNorm_small hA
      have hr : r < 1/(((C+1 : ℕ) : ℝ)+1) := by
        dsimp [r]
        push_cast
        apply one_div_lt_one_div_of_lt (by positivity)
        linarith
      exact hx.1.trans_lt hr
    · exact fun x hx => hx.2
  refine ⟨centralQuotientRadius_pos C hB hD,
    (min_le_right _ _).trans (centralizingEscapeRadius_le_half D),hcentral,
    centralEscapeWindow A u r,hV,?_⟩
  have hsub : escapeSublevel A δ ⊆ centralEscapeWindow A u (r/(6*B)) := by
    intro x hx
    refine ⟨?_,hcentral x hx⟩
    change escapeNorm A x ≤ r/(6*B)
    exact le_trans hx (min_le_left _ _)
  have he : B*(6 : ℕ)*(r/(6*B)) = r := by field_simp; ring
  exact (Set.pow_subset_pow_left hsub).trans (by
    simpa only [he] using centralEscapeWindow_power_subset hB.le hprod u (r/(6*B)) 6)
end DirectedCycles
