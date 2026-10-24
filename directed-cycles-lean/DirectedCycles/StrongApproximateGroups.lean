import DirectedCycles.FiniteGleasonProduct
import DirectedCycles.FiniteGleasonCommutator

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

def setConjugates (S B : Set G) : Set G :=
  {x | ∃ s ∈ S, ∃ b ∈ B, x = b⁻¹*s*b}

theorem setConjugates_inv {S B : Set G} (hS : S⁻¹ = S) :
    (setConjugates S B)⁻¹ = setConjugates S B := by
  have hclosed : ∀ x ∈ setConjugates S B, x⁻¹ ∈ setConjugates S B := by
    rintro x ⟨s,hs,b,hb,rfl⟩
    have hsi : s⁻¹ ∈ S := by
      have h : s⁻¹ ∈ S⁻¹ := Set.inv_mem_inv.mpr hs
      simpa only [hS] using h
    exact ⟨s⁻¹,hsi,b,hb,by group⟩
  ext x
  constructor
  · intro hx
    change x⁻¹ ∈ setConjugates S B at hx
    simpa using hclosed x⁻¹ hx
  · intro hx
    change x⁻¹ ∈ setConjugates S B
    exact hclosed x hx

theorem one_mem_setConjugates {S B : Set G} (hS : 1 ∈ S) (hB : 1 ∈ B) :
    (1 : G) ∈ setConjugates S B := ⟨1,hS,1,hB,by simp⟩

/-- The finite global strong approximate-group predicate, using the numerical
trapping radii of BGT Definition 7.1. This is a definition of a property, not
an assertion that arbitrary approximate groups possess it. -/
structure IsStrongFiniteApproximateGroup (K : ℕ) (A : Finset G) : Prop where
  one_le : 1 ≤ K
  approximate : IsApproximateSubgroup (K : ℝ) (A : Set G)
  trapping : ∃ S : Set G, S⁻¹ = S ∧
    (setConjugates S ((A : Set G)^4))^(1000*K^3) ⊆ A ∧
    (∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → x^j ∈ (A : Set G)^100) → x ∈ A) ∧
    (∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ 1000000*K^3 → x^j ∈ A) → x ∈ S)

variable [Fintype G]

/-- All the finite global product hypotheses are derived from the actual
strong-group predicate. The third-power support estimate repairs the numerical
mismatch between the stated strong-group radius and the paper's second bump. -/
theorem strong_approximate_product {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A) (hK : 2 ≤ K) (l : List G) :
    escapeNorm A l.prod ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (escapeNorm A)).sum := by
  obtain ⟨S,hSi,hsmall,hfirst,hsecond⟩ := hA.trapping
  let Q := setConjugates S ((A : Set G)^4)
  have hS1 : (1 : G) ∈ S := hsecond 1 (fun _ _ _ => by simpa using hA.approximate.one_mem)
  have hQ1 : (1 : G) ∈ Q := one_mem_setConjugates hS1 (Set.one_mem_pow hA.approximate.one_mem)
  have hfirst4 : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 → x^j ∈ (A : Set G)^4) → x ∈ A := by
    intro x hx
    apply hfirst
    intro j hj hjC
    exact (Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 4 ≤ 100)) (hx j hj hjC)
  have hconj : ∀ h ∈ S, ∀ y ∈ (A : Set G)^3, y⁻¹*h*y ∈ Q := by
    intro h hh y hy
    exact ⟨h,hh,y,(Set.pow_subset_pow_right hA.approximate.one_mem (by omega : 3 ≤ 4)) hy,rfl⟩
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hconst : 2*(1000 : ℝ)*(K : ℝ)^2 ≤ ((1000*K^3 : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (K : ℝ), mul_nonneg (sq_nonneg (K : ℝ)) (sub_nonneg.mpr hKr)]
  exact finite_gleason_product A (by exact_mod_cast hA.one_le) hA.approximate S Q hQ1
    (setConjugates_inv hSi) 1000 (1000000*K^3) (1000*K^3) (by omega) (by positivity)
    (by positivity) hfirst4 hsecond hconj hsmall hconst l

/-- The finite global commutator conclusion with the same concrete trapping data. -/
theorem strong_approximate_commutator {K : ℕ} {A : Finset G}
    (hA : IsStrongFiniteApproximateGroup K A) (hK : 2 ≤ K)
    {g h : G} (hg : g ∈ (A : Set G)^10) (hh : h ∈ (A : Set G)^10) :
    let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
    escapeNorm A (g⁻¹*h⁻¹*g*h) ≤
      (2*(1000 : ℝ)^2*(K : ℝ)^11*P^2)*escapeNorm A g*escapeNorm A h := by
  dsimp only
  obtain ⟨S,hSi,hsmall,hfirst,hsecond⟩ := hA.trapping
  have hK0 : 0 < K := by omega
  exact finite_gleason_commutator_of_product A (by exact_mod_cast hA.one_le)
    hA.approximate 1000 (by omega) hfirst (by positivity)
    (strong_approximate_product hA hK) hg hh
end DirectedCycles
