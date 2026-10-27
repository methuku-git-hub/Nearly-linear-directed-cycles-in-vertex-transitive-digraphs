module

public import DirectedCycles.ShortPowerReturns
public import DirectedCycles.LocalQuotientWindow

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The genuine short signed progression, rather than its generated subgroup. -/
def shortPowerProgression (u : G) (N : ℕ) : Set G :=
  {x | ∃ n : ℤ, n.natAbs < N ∧ u^n = x}

theorem one_mem_shortPowerProgression (u : G) {N : ℕ} (hN : 0 < N) :
    (1 : G) ∈ shortPowerProgression u N := ⟨0,by simpa using hN,by simp⟩

theorem inv_mem_shortPowerProgression {u x : G} {N : ℕ}
    (hx : x ∈ shortPowerProgression u N) : x⁻¹ ∈ shortPowerProgression u N := by
  obtain ⟨n,hn,rfl⟩ := hx
  exact ⟨-n,by simpa using hn,by simp⟩

theorem shortPowerProgression_symmetric (u : G) (N : ℕ) :
    (shortPowerProgression u N)⁻¹ = shortPowerProgression u N := by
  ext x
  constructor
  · intro hx
    have h := inv_mem_shortPowerProgression (Set.mem_inv.mp hx)
    simpa using h
  · intro hx
    exact Set.mem_inv.mpr (inv_mem_shortPowerProgression hx)

theorem shortPowerProgression_subset {A : Set G} (hi : A⁻¹ = A) (u : G) (N : ℕ)
    (hprev : ∀ i < N, u^i ∈ A) : shortPowerProgression u N ⊆ A := by
  rintro x ⟨n,hn,rfl⟩
  obtain ⟨m,rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using hprev m (by simpa using hn)
  · have hm := hprev m (by simpa using hn)
    have h : (u^m)⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr hm
    simpa [hi] using h

/-- The signed version of the no-short-return lemma. -/
theorem no_short_zpow_return {A : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (u : G) {N : ℕ} {m : ℤ} (hN : 0 < N) (hNm : N ≤ m.natAbs)
    (hmN : m.natAbs < 2*N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A)
    (hreturn : ∀ j ≤ C+1, (u^m)^j ∈ A) : False := by
  obtain ⟨k,rfl | rfl⟩ := Int.eq_nat_or_neg m
  · apply no_short_power_return hi C htrap u hN (by simpa using hNm)
      (by simpa using hmN) hexit hprev
    simpa using hreturn
  · apply no_short_power_return hi C htrap u hN (by simpa using hNm)
      (by simpa using hmN) hexit hprev
    intro j hj
    have h : ((u^(-(k : ℤ)))^j)⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr (hreturn j hj)
    simpa [hi] using h

/-- A first-exit progression is locally closed inside a region of sufficiently
small escape, and is locally normal there if that region centralizes u. -/
theorem shortPowerProgression_localNormal {A V : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (u : G) {N : ℕ} (hN : 0 < N) (hexit : u^N ∉ A) (hprev : ∀ i < N, u^i ∈ A)
    (hsmall : ∀ x ∈ V, ∀ j ≤ C+1, x^j ∈ A)
    (hcentral : ∀ x ∈ V, Commute x u) : LocalNormalSet (shortPowerProgression u N) V where
  one_mem := one_mem_shortPowerProgression u hN
  inv_mem _ hx := inv_mem_shortPowerProgression hx
  mul_mem := by
    rintro x ⟨n,hn,rfl⟩ y ⟨m,hm,rfl⟩ hV
    have hnm : (n+m).natAbs < N := by
      by_contra h
      apply no_short_zpow_return hi C htrap u hN (by omega)
        (lt_of_le_of_lt (Int.natAbs_add_le n m) (by omega)) hexit hprev
      intro j hj
      rw [zpow_add]
      exact hsmall _ hV j hj
    exact ⟨n+m,hnm,zpow_add u n m⟩
  conj_mem := by
    rintro x hx p ⟨n,hn,rfl⟩ _
    have he : x*u^n*x⁻¹ = u^n := by rw [(hcentral x hx).zpow_right n |>.eq]; simp [mul_assoc]
    rw [he]
    exact ⟨n,hn,rfl⟩
end DirectedCycles
