import DirectedCycles.BoundedGroupDerivative

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The pointwise Taylor estimate in terms of the actual escape norm,
including the case of an infinite power segment. -/
theorem boundedDerivative_le_escape_of_second {f : G → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x, |f x| ≤ K) (g : G) {S : Set G}
    (hS : (1 : G) ∈ S) {R : ℝ} (hR : 0 ≤ R)
    (hsecond : ∀ h ∈ S, ∀ x, |groupDerivative h (groupDerivative g f) x| ≤ R) :
    boundedDerivative f g ≤ 4*K*escapeNorm S g+R := by
  have hsegment : ∀ n : ℕ, 0 < n → (∀ i < n, g^i ∈ S) →
      boundedDerivative f g ≤ 2*K/(n : ℝ)+R := by
    intro n hn hp
    apply (boundedDerivative_le_iff hf g _).2
    exact groupDerivative_taylor_pointwise f g hn (groupDerivative_le_two_bound hf (g^n))
      (fun i hi => hsecond _ (hp i hi))
  classical
  by_cases hex : ∃ n : ℕ, g^n ∉ S
  · let n := Nat.find hex
    have hn : g^n ∉ S := Nat.find_spec hex
    have hp : ∀ i < n, g^i ∈ S := fun i hi => not_not.mp (Nat.find_min hex hi)
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      exact hn (by simpa [this] using hS)
    rw [escapeNorm_eq_inv_of_first_exit hS hn hp]
    by_cases hn1 : n = 1
    · simp only [hn1,Nat.cast_one,div_one,mul_one]
      have h := boundedDerivative_le_two_bound hf g
      linarith
    · have hm0 : 0 < n-1 := by omega
      have hnr : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hmr : 0 < ((n-1 : ℕ) : ℝ) := by exact_mod_cast hm0
      have hnm : (n : ℝ) ≤ 2*((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ 2*(n-1))
      apply (hsegment (n-1) hm0 (fun i hi => hp i (by omega))).trans
      apply add_le_add _ le_rfl
      rw [mul_one_div]
      apply (div_le_div_iff₀ hmr hnr).2
      nlinarith
  · have hall : ∀ n : ℕ, g^n ∈ S := by simpa using hex
    rw [(escapeNorm_eq_zero_iff hS g).2 hall,mul_zero,zero_add]
    by_contra h
    have hδ : 0 < boundedDerivative f g-R := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (2*K/(boundedDerivative f g-R))
    have hn0r : 0 < (n : ℝ) := (div_nonneg (by positivity) hδ.le).trans_lt hn
    have hn0 : 0 < n := by exact_mod_cast hn0r
    have ht := hsegment n hn0 (fun i _ => hall i)
    have hprod := (div_lt_iff₀ hδ).mp hn
    have hprod' : (boundedDerivative f g-R)*(n : ℝ) ≤ 2*K :=
      (le_div_iff₀ hn0r).mp (by linarith : boundedDerivative f g-R ≤ 2*K/(n : ℝ))
    nlinarith
end DirectedCycles
