import DirectedCycles.LocalFiniteTranslations

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

noncomputable def chainCount (E : ℕ → Set G) (N : ℕ) (x : G) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range N, if x ∈ E i then 1 else 0

theorem chainCount_bounds (E : ℕ → Set G) (N : ℕ) (x : G) :
    0 ≤ chainCount E N x ∧ chainCount E N x ≤ N := by
  classical
  constructor
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  · calc
      chainCount E N x ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
      _ = N := by simp

/-- Shifting membership up by one level changes the chain count by at most
one. No nesting assumption is needed for this elementary counting step. -/
theorem chainCount_step_le (E : ℕ → Set G) (N : ℕ) (x y : G)
    (h : ∀ i < N, y ∈ E i → x ∈ E (i+1)) :
    chainCount E N y ≤ chainCount E N x+1 := by
  classical
  let w : ℕ → ℝ := fun i => if x ∈ E i then 1 else 0
  have hc : chainCount E N y ≤ ∑ i ∈ Finset.range N, w (i+1) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hy : y ∈ E i
    · have hx := h i (Finset.mem_range.mp hi) hy
      simp only [ite_eq_left hy,w,ite_eq_left hx,le_refl]
    · simp only [ite_eq_right hy,w]
      split_ifs <;> norm_num
  have h0 : 0 ≤ w 0 := by dsimp [w]; split_ifs <;> norm_num
  have hN : w N ≤ 1 := by dsimp [w]; split_ifs <;> norm_num
  have hsum' := Finset.sum_range_succ' w N
  rw [Finset.sum_range_succ] at hsum'
  change chainCount E N y ≤ (∑ i ∈ Finset.range N, w i)+1
  linarith

/-- A finite chain of neighbourhoods with actual local translation witnesses
produces a bounded bump and its 1/N derivative estimate. Undefined products
are handled using the inverse translation domain, not assigned group values. -/
theorem exists_chain_bump (hd : L.DivisionClosed) (hc : L.Cancellative)
    (Q A B : Set G) (E : ℕ → Set G) (N : ℕ) (hN : 0 < N)
    (hQi : ∀ q ∈ Q, L.inv q ∈ Q)
    (hA : ∀ i < N, A ⊆ E i) (hB : ∀ i < N, E i ⊆ B)
    (hmove : ∀ q ∈ Q, ∀ i < N, ∀ x ∈ E i, ∃ y ∈ E (i+1), L.mulRel q x y) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧ (∀ x, x ∉ B → φ x = 0) ∧
      (∀ q ∈ Q, ∀ x, |L.derivative q φ x| ≤ 1/(N : ℝ)) := by
  classical
  let φ := fun x => chainCount E N x/(N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  refine ⟨φ,?_,?_,?_,?_⟩
  · intro x
    have hb := chainCount_bounds E N x
    exact ⟨div_nonneg hb.1 hNr.le,(div_le_one hNr).2 hb.2⟩
  · intro x hx
    have he : chainCount E N x = N := by
      unfold chainCount
      have ht : ∀ i ∈ Finset.range N, (if x ∈ E i then (1 : ℝ) else 0) = 1 :=
        fun i hi => ite_eq_left (hA i (Finset.mem_range.mp hi) hx)
      simp_rw [Finset.sum_congr rfl ht]
      simp
    change chainCount E N x/(N : ℝ) = 1
    rw [he,div_self hNr.ne']
  · intro x hx
    have he : chainCount E N x = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun hm => hx (hB i (Finset.mem_range.mp hi) hm))
    change chainCount E N x/(N : ℝ) = 0
    rw [he,zero_div]
  · intro q hq x
    by_cases hex : ∃ y, L.mulRel q y x
    · obtain ⟨y,hy⟩ := hex
      have hforward : ∀ i < N, y ∈ E i → x ∈ E (i+1) := by
        intro i hi hyE
        obtain ⟨z,hz,hm⟩ := hmove q hq i hi y hyE
        exact (L.unique hm hy) ▸ hz
      have hback : ∀ i < N, x ∈ E i → y ∈ E (i+1) := by
        intro i hi hxE
        obtain ⟨z,hz,hm⟩ := hmove (L.inv q) (hQi q hq) i hi x hxE
        exact (L.unique hm (hd.left hy)) ▸ hz
      have hdiff : |chainCount E N y-chainCount E N x| ≤ 1 := by
        rw [abs_le]
        have hxy := chainCount_step_le E N x y hforward
        have hyx := chainCount_step_le E N y x hback
        constructor <;> linarith
      change |L.leftShift q φ x-φ x| ≤ _
      rw [L.leftShift_of_mulRel hc hy]
      change |chainCount E N y/(N : ℝ)-chainCount E N x/(N : ℝ)| ≤ _
      rw [← sub_div,abs_div,abs_of_pos hNr]
      exact div_le_div_of_nonneg_right hdiff hNr.le
    · have hx : chainCount E N x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply ite_eq_right
        intro hm
        obtain ⟨y,_,hy⟩ := hmove (L.inv q) (hQi q hq) i (Finset.mem_range.mp hi) x hm
        apply hex
        exact ⟨y,by simpa only [L.inv_inv] using hd.left hy⟩
      change |L.leftShift q φ x-φ x| ≤ _
      rw [L.leftShift_of_no_preimage hex]
      change |0-chainCount E N x/(N : ℝ)| ≤ _
      rw [hx,zero_div,sub_self,abs_zero]
      positivity
end LocalGroupAlgebra
end DirectedCycles
