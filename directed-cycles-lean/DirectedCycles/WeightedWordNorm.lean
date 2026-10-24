import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Costs of all words with a prescribed product, including the empty word. -/
def wordCosts (w : G → ℝ) (g : G) : Set ℝ :=
  {x | ∃ l : List G, l.prod = g ∧ x = (l.map w).sum}

noncomputable def wordNorm (w : G → ℝ) (g : G) : ℝ := sInf (wordCosts w g)

theorem wordCosts_nonempty (w : G → ℝ) (g : G) : (wordCosts w g).Nonempty :=
  ⟨w g, [g], by simp, by simp⟩

theorem wordCosts_bddBelow {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    BddBelow (wordCosts w g) := by
  refine ⟨0, ?_⟩
  rintro x ⟨l, _, rfl⟩
  exact List.sum_nonneg (by simpa using fun g (_ : g ∈ l) => hw g)

theorem wordNorm_nonneg {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    0 ≤ wordNorm w g := by
  apply le_csInf (wordCosts_nonempty w g)
  rintro x ⟨l, _, rfl⟩
  exact List.sum_nonneg (by simpa using fun a (_ : a ∈ l) => hw a)

theorem wordNorm_le_cost {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (l : List G) :
    wordNorm w l.prod ≤ (l.map w).sum :=
  csInf_le (wordCosts_bddBelow hw l.prod) ⟨l, rfl, rfl⟩

theorem wordNorm_le_weight {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    wordNorm w g ≤ w g := by simpa using wordNorm_le_cost hw [g]

theorem wordNorm_one {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) : wordNorm w 1 = 0 := by
  apply le_antisymm _ (wordNorm_nonneg hw 1)
  simpa using wordNorm_le_cost hw ([] : List G)

theorem wordNorm_mul_le {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g h : G) :
    wordNorm w (g*h) ≤ wordNorm w g + wordNorm w h := by
  apply (sub_le_iff_le_add).mp
  apply le_csInf (wordCosts_nonempty w g)
  rintro x ⟨l, hl, rfl⟩
  rw [sub_le_iff_le_add]
  apply (sub_le_iff_le_add').mp
  apply le_csInf (wordCosts_nonempty w h)
  rintro x ⟨k, hk, rfl⟩
  rw [sub_le_iff_le_add']
  simpa [hl, hk] using wordNorm_le_cost hw (l++k)

theorem wordNorm_inv {w : G → ℝ} (hi : ∀ g, w g⁻¹ = w g) (g : G) :
    wordNorm w g⁻¹ = wordNorm w g := by
  have hle : ∀ a : G, wordCosts w a ⊆ wordCosts w a⁻¹ := by
    intro a x
    rintro ⟨l, hl, rfl⟩
    refine ⟨(l.map Inv.inv).reverse, ?_, ?_⟩
    · simpa [← hl] using (List.prod_inv_reverse l).symm
    · simp [List.map_map, Function.comp_def, hi]
  have he : wordCosts w g⁻¹ = wordCosts w g := by
    apply Set.Subset.antisymm
    · simpa using hle g⁻¹
    · exact hle g
  simp only [wordNorm, he]

/-- Regularization separates every nonidentity element from zero, while the
empty word keeps the distance of the identity exactly zero. -/
theorem le_wordNorm_of_weight_lower {w : G → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hw : ∀ g, ε ≤ w g) {g : G} (hg : g ≠ 1) :
    ε ≤ wordNorm w g := by
  apply le_csInf (wordCosts_nonempty w g)
  rintro x ⟨l, hl, rfl⟩
  cases l with
  | nil => simp at hl; exact (hg hl.symm).elim
  | cons a l =>
    have htail : 0 ≤ (l.map w).sum :=
      List.sum_nonneg (by simpa using fun b (_ : b ∈ l) => hε.trans (hw b))
    simpa using (hw a).trans (le_add_of_nonneg_right htail)

/-- The infimum of word costs is the greatest subadditive function below the weights. -/
theorem le_wordNorm {w v : G → ℝ} (hv1 : v 1 ≤ 0)
    (hvmul : ∀ g h, v (g*h) ≤ v g + v h) (hvw : ∀ g, v g ≤ w g) (g : G) :
    v g ≤ wordNorm w g := by
  apply le_csInf (wordCosts_nonempty w g)
  rintro x ⟨l, rfl, rfl⟩
  induction l with
  | nil => simpa using hv1
  | cons a l ih =>
    simpa using (hvmul a l.prod).trans (add_le_add (hvw a) ih)

/-- A scaled version used to improve derivative bounds by the bootstrap argument. -/
theorem le_mul_wordNorm {w v : G → ℝ} {C : ℝ} (hC : 0 < C)
    (hv1 : v 1 ≤ 0) (hvmul : ∀ g h, v (g*h) ≤ v g + v h)
    (hvw : ∀ g, v g ≤ C*w g) (g : G) : v g ≤ C*wordNorm w g := by
  have hh : v g / C ≤ wordNorm w g := by
    apply le_wordNorm (v := fun x => v x / C)
    · exact div_nonpos_of_nonpos_of_nonneg hv1 hC.le
    · intro a b
      simpa [add_div] using div_le_div_of_nonneg_right (hvmul a b) hC.le
    · intro a
      exact (div_le_iff₀ hC).2 (by simpa [mul_comm] using hvw a)
  simpa [mul_comm] using (div_le_iff₀ hC).1 hh
end DirectedCycles
