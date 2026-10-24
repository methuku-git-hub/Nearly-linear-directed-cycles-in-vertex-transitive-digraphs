import DirectedCycles.NormSetBump

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

noncomputable def wordBallWeight (Q : Set G) (N : ℕ) (g : G) : ℝ := by
  classical
  exact if g ∈ Q then 1 else N

omit [Group G] in
theorem wordBallWeight_one_le (Q : Set G) {N : ℕ} (hN : 1 ≤ N) (g : G) :
    1 ≤ wordBallWeight Q N g := by
  classical
  unfold wordBallWeight
  split_ifs
  · rfl
  · exact_mod_cast hN

omit [Group G] in
theorem weight_le_word_cost {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {l : List G} {g : G} (hg : g ∈ l) : w g ≤ (l.map w).sum := by
  induction l with
  | nil => simp at hg
  | cons a l ih =>
    simp only [List.mem_cons] at hg
    simp only [List.map_cons, List.sum_cons]
    rcases hg with rfl | hg
    · exact le_add_of_nonneg_right (List.sum_nonneg (by simpa using fun b (_ : b ∈ l) => hw b))
    · exact (ih hg).trans (le_add_of_nonneg_left (hw a))

omit [Group G] in
theorem length_le_wordBall_cost (Q : Set G) {N : ℕ} (hN : 1 ≤ N) (l : List G) :
    (l.length : ℝ) ≤ (l.map (wordBallWeight Q N)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa [add_comm] using add_le_add (wordBallWeight_one_le Q hN a) ih

theorem list_prod_mem_set_pow {Q : Set G} (l : List G) (hl : ∀ g ∈ l, g ∈ Q) :
    l.prod ∈ Q^l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ']
    exact Set.mul_mem_mul (hl a (by simp)) (ih (fun g hg => hl g (by simp [hg])))

/-- A word of cost below N uses only generators in Q and fewer than N letters. -/
theorem prod_mem_wordBall_of_cost_lt {Q : Set G} (hQ : 1 ∈ Q) {N : ℕ} (hN : 1 ≤ N)
    (l : List G) (hl : (l.map (wordBallWeight Q N)).sum < N) : l.prod ∈ Q^N := by
  have hnonneg : ∀ g, 0 ≤ wordBallWeight Q N g := fun g =>
    zero_le_one.trans (wordBallWeight_one_le Q hN g)
  have hletters : ∀ g ∈ l, g ∈ Q := by
    intro g hg
    by_contra hgQ
    have h := weight_le_word_cost hnonneg hg
    have he : wordBallWeight Q N g = N := by simp [wordBallWeight, hgQ]
    rw [he] at h
    linarith
  have hlen : l.length ≤ N := by
    have := (length_le_wordBall_cost Q hN l).trans_lt hl
    exact_mod_cast this.le
  exact (Set.pow_subset_pow_right hQ hlen) (list_prod_mem_set_pow l hletters)

theorem wordBall_separation {Q A : Set G} (hQ : 1 ∈ Q) {N : ℕ} (hN : 1 ≤ N)
    (hQA : Q^N ⊆ A) {g : G} (hg : g ∉ A) :
    (N : ℝ) ≤ wordNorm (wordBallWeight Q N) g := by
  apply le_csInf (wordCosts_nonempty _ g)
  rintro x ⟨l, rfl, rfl⟩
  by_contra h
  exact hg (hQA (prod_mem_wordBall_of_cost_lt hQ hN l (lt_of_not_ge h)))

/-- The second BGT bump for any symmetric word ball contained in A.
The radius N is an explicit parameter, allowing the trapping constants to be
chosen consistently in the later strong-group construction. -/
theorem exists_wordBall_bump (A : Finset G) (hA : (1 : G) ∈ A) (Q : Set G)
    (hQ : 1 ∈ Q) (hQi : Q⁻¹ = Q) {N : ℕ} (hN : 1 ≤ N) (hQA : Q^N ⊆ A) :
    ∃ ψ : G → ℝ, (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x ∈ A, ψ x = 1) ∧
      (∀ x, x ∉ (A : Set G)^2 → ψ x = 0) ∧
      (∀ q ∈ Q, ∀ x, |ψ (q⁻¹*x)-ψ x| ≤ 1/(N : ℝ)) := by
  classical
  let w := wordBallWeight Q N
  have hw : ∀ g, 0 ≤ w g := fun g => zero_le_one.trans (wordBallWeight_one_le Q hN g)
  have hwi : ∀ g, w g⁻¹ = w g := by
    intro g
    have he : g⁻¹ ∈ Q ↔ g ∈ Q := by
      calc
        g⁻¹ ∈ Q ↔ g⁻¹ ∈ Q⁻¹ := by rw [hQi]
        _ ↔ g ∈ Q := by simp
    simp only [w, wordBallWeight, he]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨ψ,hψ,hψA,hψs,hψlip⟩ := exists_norm_bump (wordNorm_nonneg hw) (wordNorm_one hw)
    (wordNorm_mul_le hw) (wordNorm_inv hwi) A ⟨1,hA⟩ hNr
    (fun _ hg => wordBall_separation hQ hN hQA hg)
  refine ⟨ψ,hψ,hψA,hψs,?_⟩
  intro q hq x
  apply (hψlip q x).trans
  apply div_le_div_of_nonneg_right _ hNr.le
  have h := wordNorm_le_weight hw q
  simpa [w,wordBallWeight,hq] using h
end DirectedCycles
