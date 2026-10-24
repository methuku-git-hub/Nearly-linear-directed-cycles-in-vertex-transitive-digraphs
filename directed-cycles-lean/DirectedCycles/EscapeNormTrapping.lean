import DirectedCycles.EscapeNorm

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Transfer initial power segments through an integer contraction of their lengths. -/
theorem escapeNorm_le_mul_of_segments {A B : Set G} {a b : G} (hA : 1 ∈ A)
    (C : ℕ) (hC : 0 < C)
    (h : ∀ n : ℕ, (∀ i ≤ n, a^i ∈ A) → ∀ j ≤ n/C, b^j ∈ B) :
    escapeNorm B b ≤ (C : ℝ) * escapeNorm A a := by
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  suffices hh : escapeNorm B b / C ≤ escapeNorm A a by
    simpa [mul_comm] using (div_le_iff₀ hCr).mp hh
  apply le_csInf (escapeValues_nonempty hA a)
  rintro x ⟨n, hn, rfl⟩
  rw [div_le_iff₀ hCr]
  have hb := escapeNorm_le_of_powers (h n hn)
  have hdiv : n+1 ≤ (n/C+1)*C := by
    have hr := Nat.mod_lt n hC
    have he := Nat.div_add_mod n C
    nlinarith
  have hr : (n : ℝ)+1 ≤ ((n/C : ℕ)+1 : ℝ)*C := by exact_mod_cast hdiv
  calc
    escapeNorm B b ≤ 1 / ((n/C : ℕ)+1 : ℝ) := hb
    _ ≤ 1 / ((n : ℝ)+1) * C := by
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa [mul_comm] using hr

/-- A power-trapping condition gives an escape-norm bound between two sets. -/
theorem escapeNorm_le_mul_of_trapping {A B : Set G} (hB : 1 ∈ B)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ B) → x ∈ A)
    (g : G) : escapeNorm A g ≤ (C : ℝ)*escapeNorm B g := by
  apply escapeNorm_le_mul_of_segments hB C hC
  intro n hn i hi
  apply htrap
  intro j _ hj
  rw [← pow_mul]
  apply hn
  calc
    i*j ≤ (n/C)*C := Nat.mul_le_mul hi hj
    _ ≤ n := Nat.div_mul_le_self n C

/-- Conjugation preserves each initial power segment in the conjugated set. -/
theorem conjugate_powers_mem {A B : Set G} (h : G) {g : G} {n : ℕ}
    (hAB : ∀ x ∈ A, h⁻¹*x*h ∈ B) (hg : ∀ i ≤ n, g^i ∈ A) :
    ∀ i ≤ n, (h⁻¹*g*h)^i ∈ B := by
  intro i hi
  have he : ∀ k : ℕ, (h⁻¹*g*h)^k = h⁻¹*g^k*h := by
    intro k
    induction k with
    | zero => simp
    | succ i ih => rw [pow_succ, ih, pow_succ]; group
  rw [he i]
  exact hAB _ (hg i hi)

/-- The first BGT trapping property proves the conjugation estimate,
with its constant and all set containments explicit. -/
theorem escapeNorm_conjugate_of_trapping {A B : Set G} (hA : 1 ∈ A)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ B) → x ∈ A)
    (h : G) (hAB : ∀ x ∈ A, h⁻¹*x*h ∈ B) (g : G) :
    escapeNorm A (h⁻¹*g*h) ≤ (C : ℝ)*escapeNorm A g := by
  apply escapeNorm_le_mul_of_segments hA C hC
  intro n hn i hi
  apply htrap
  intro j _ hj
  rw [← pow_mul]
  apply conjugate_powers_mem h hAB hn
  exact (Nat.mul_le_mul hi hj).trans (Nat.div_mul_le_self n C)
end DirectedCycles
