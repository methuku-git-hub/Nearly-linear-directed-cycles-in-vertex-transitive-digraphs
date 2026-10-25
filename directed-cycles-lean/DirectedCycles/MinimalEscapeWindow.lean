module

public import DirectedCycles.MinimalEscapeCentrality
public import DirectedCycles.CentralEscapeWindow

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Positive escape has an actual first exiting power. -/
theorem exists_first_escape {A : Set G} (hA : 1 ∈ A) {u : G}
    (hu : 0 < escapeNorm A u) :
    ∃ N : ℕ, 0 < N ∧ u^N ∉ A ∧ (∀ i < N, u^i ∈ A) := by
  classical
  have hex : ∃ N : ℕ, u^N ∉ A := by
    by_contra h
    have hall : ∀ N : ℕ, u^N ∈ A := by simpa using h
    rw [(escapeNorm_eq_zero_iff hA u).2 hall] at hu
    exact lt_irrefl _ hu
  let N := Nat.find hex
  have hn : u^N ∉ A := Nat.find_spec hex
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    exact hn (by simpa [this] using hA)
  exact ⟨N,hN,hn,fun i hi => not_not.mp (Nat.find_min hex hi)⟩

/-- The commutator estimate forces an entire explicitly small escape sublevel
to centralize a least-positive-escape element. -/
theorem exists_centralizing_escapeSublevel {A : Set G} (hA : 1 ∈ A) {u : G}
    (hu : 0 < escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v)
    {D : ℝ} (hD : 0 ≤ D)
    (hcomm : ∀ x ∈ A, escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ x ∈ escapeSublevel A δ, Commute x u := by
  let δ : ℝ := min (1/2) (1/(2*(D+1)))
  have hden : 0 < 2*(D+1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (one_div_pos.mpr hden)
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  intro x hx
  have hx' : escapeNorm A x ≤ δ := hx
  have hxA : x ∈ A := mem_of_escapeNorm_lt_one hA (lt_of_le_of_lt
    (hx'.trans (min_le_left _ _)) (by norm_num))
  apply minimal_escape_commutes hA hu hmin (hcomm x hxA)
  have hδb : δ ≤ 1/(2*(D+1)) := min_le_right _ _
  have hδb' := (le_div_iff₀ hden).1 hδb
  have hDx := mul_le_mul_of_nonneg_left hx' hD
  nlinarith

/-- The local quotient window can be an ordinary escape sublevel, rather than
an intersection with an unquantified centralizer. All its properties are
proved from the stated product, trapping and commutator estimates. -/
theorem minimal_escape_quotient_window {A : Set G} (hA : 1 ∈ A) (hi : A⁻¹ = A)
    (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D)
    (hprod : ∀ l : List G, escapeNorm A l.prod ≤ B*(l.map (escapeNorm A)).sum)
    {u : G} (hu : 0 < escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v)
    (hcomm : ∀ x ∈ A, escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u) :
    ∃ N : ℕ, 0 < N ∧ u^N ∉ A ∧ (∀ i < N, u^i ∈ A) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ (∀ x ∈ escapeSublevel A δ, Commute x u) ∧
        ∃ V : Set G, LocalNormalSet (shortPowerProgression u N) V ∧
          (escapeSublevel A δ)^6 ⊆ V := by
  obtain ⟨N,hN,hexit,hprev⟩ := exists_first_escape hA hu
  obtain ⟨δ₀,hδ₀,V,hV,_,_,hpow⟩ :=
    exists_shortProgression_quotient_window hA hi C htrap hB hprod u hN hexit hprev
  obtain ⟨δ₁,hδ₁,hδ₁half,hcentral⟩ := exists_centralizing_escapeSublevel hA hu hmin hD hcomm
  let δ := min δ₀ δ₁
  have hcentral' : ∀ x ∈ escapeSublevel A δ, Commute x u := by
    intro x hx
    apply hcentral x
    change escapeNorm A x ≤ δ₁
    exact le_trans hx (min_le_right δ₀ δ₁)
  refine ⟨N,hN,hexit,hprev,δ,lt_min hδ₀ hδ₁,(min_le_right _ _).trans hδ₁half,hcentral',V,hV,?_⟩
  apply Set.Subset.trans _ hpow
  apply Set.pow_subset_pow_left
  intro x hx
  refine ⟨?_,hcentral' x hx⟩
  change escapeNorm A x ≤ δ₀
  exact le_trans hx (min_le_left δ₀ δ₁)
end DirectedCycles
