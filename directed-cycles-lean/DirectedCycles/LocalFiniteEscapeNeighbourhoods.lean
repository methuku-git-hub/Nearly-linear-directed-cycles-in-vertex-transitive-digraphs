module

public import DirectedCycles.LocalFiniteSmallNeighbourhoods
public import DirectedCycles.LocalEscapeNorm

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A bounded trapping condition upgrades local small neighbourhoods from
A^4-containment to A-containment, uniformly over finite local groups. -/
theorem local_finite_trapped_neighbourhoods (K : ℕ) (hK : 1 ≤ K) (C : ℕ) (hC : 1 ≤ C) (m : ℕ) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G), L.DivisionClosed → L.Reversible →
      ∀ A : Finset G, IsLocalFiniteApproximateGroup L K A →
      (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A) →
      ∃ B : Finset G, IsLocalFiniteApproximateGroup L J B ∧
        δ*A.card ≤ B.card ∧ L.AllProductsDefined (B : Set G) m ∧
        (∀ n ≤ m, L.wordPower (B : Set G) n ⊆ (A : Set G)) := by
  obtain ⟨J,δ,hJ,hδ,hsmall⟩ := local_finite_small_neighbourhoods K hK (m*C)
  refine ⟨J,δ,hJ,hδ,?_⟩
  intro G _ L hd hr A hA htrap
  obtain ⟨B,hB,hBd,hdom,hpowers⟩ := hsmall G L hd hr A hA
  have hm : m ≤ m*C := by nlinarith
  refine ⟨B,hB,hBd,hdom.mono L (Set.Subset.refl _) hm,?_⟩
  intro n hn x hx
  apply htrap x
  intro j _ hj
  have hnj : n*j ≤ m*C := Nat.mul_le_mul hn hj
  obtain ⟨y,hy,hp⟩ := L.powerIn_wordPower hdom hnj hx
  exact ⟨y,hpowers (n*j) hnj hy,hp⟩

/-- Prescribed powers of a uniformly dense finite local approximate group
can be made arbitrarily small in escape norm. Long power domains are proved
by word compression; they are not inferred from global power identities. -/
theorem local_finite_escape_neighbourhoods (K : ℕ) (hK : 1 ≤ K) (C : ℕ) (hC : 1 ≤ C)
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ (J : ℕ) (δ : ℝ), 1 ≤ J ∧ 0 < δ ∧
      ∀ (G : Type*) [Fintype G] (L : LocalGroupAlgebra G), L.DivisionClosed → L.Reversible →
      ∀ A : Finset G, IsLocalFiniteApproximateGroup L K A →
      (∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower (A : Set G) 4) x j) → x ∈ A) →
      ∃ B : Finset G, IsLocalFiniteApproximateGroup L J B ∧
        δ*A.card ≤ B.card ∧ L.AllProductsDefined (B : Set G) m ∧
        (∀ n ≤ m, ∀ x ∈ L.wordPower (B : Set G) n, L.escapeNorm (A : Set G) x < r) := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hr
  obtain ⟨J,δ,hJ,hδ,hsmall⟩ := local_finite_trapped_neighbourhoods K hK C hC (m*(N+1))
  refine ⟨J,δ,hJ,hδ,?_⟩
  intro G _ L hd hrev A hA htrap
  obtain ⟨B,hB,hBd,hdom,hpowers⟩ := hsmall G L hd hrev A hA htrap
  have hm : m ≤ m*(N+1) := by nlinarith
  refine ⟨B,hB,hBd,hdom.mono L (Set.Subset.refl _) hm,?_⟩
  intro n hn x hx
  apply lt_of_le_of_lt (L.escapeNorm_le_of_powers (n := N) ?_) hN
  intro j hj
  have hnj : n*j ≤ m*(N+1) := Nat.mul_le_mul hn (by omega)
  obtain ⟨y,hy,hp⟩ := L.powerIn_wordPower hdom hnj hx
  exact ⟨y,hpowers (n*j) hnj hy,hp⟩
end DirectedCycles
