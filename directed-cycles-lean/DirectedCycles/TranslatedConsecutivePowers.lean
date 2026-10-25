module

public import DirectedCycles.FibreSpanning

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Consecutive-power spanning remains valid after arbitrary left translation. -/
theorem translated_consecutive_powers_mem {G : Type*} [Group G]
    (D : ℕ) (a x : G) (W : AddSubgroup (TruncatedGroupRing G D))
    (h : ∀ k : ℕ, k < D → truncatedElement G D (x*a^k) ∈ W) :
    ∀ k : ℤ, truncatedElement G D (x*a^k) ∈ W := by
  let φ := AddMonoidHom.mulLeft (truncatedElement G D x)
  have hh : ∀ i : ℕ, i < D → truncatedElement G D (a^(0+(i : ℤ))) ∈ W.comap φ := by
    intro i hi
    change truncatedElement G D x * truncatedElement G D (a^(0+(i : ℤ))) ∈ W
    rw [zero_add,zpow_natCast,← map_mul]
    exact h i hi
  intro k
  have hk := truncated_consecutive_powers_mem D a (W.comap φ) 0 hh k
  change truncatedElement G D x * truncatedElement G D (a^k) ∈ W at hk
  rwa [← map_mul] at hk

end DirectedCycles
