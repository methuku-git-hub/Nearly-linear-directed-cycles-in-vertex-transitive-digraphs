module

public import DirectedCycles.TranslateEnergy

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem sum_membership_indicator (R T : Finset β) (hTR : T ⊆ R) :
    (∑ x ∈ R, if x ∈ T then (1 : ℝ) else 0) = T.card := by
  have he : R.filter (fun x => x ∈ T) = T := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hTR h,h⟩⟩
  rw [← Finset.sum_filter,he]
  simp

omit [DecidableEq α] in
/-- Cauchy--Schwarz for an arbitrary finite family of equally sized subsets.
This counting theorem needs no global group action and hence applies to
local translates once their actual domains and cardinalities are proved. -/
theorem finite_family_overlap_row (I : Finset α) (R : Finset β) (T : α → Finset β)
    (m : ℕ) (hI : I.Nonempty) (hTR : ∀ a ∈ I, T a ⊆ R) (hsize : ∀ a ∈ I, (T a).card = m) :
    ∃ a ∈ I, (I.card : ℝ)*(m : ℝ)^2 ≤
      R.card*(∑ b ∈ I, ((T a ∩ T b).card : ℝ)) := by
  classical
  let d := fun x => ∑ a ∈ I, if x ∈ T a then (1 : ℝ) else 0
  have htotal : (∑ x ∈ R, d x) = (I.card : ℝ)*m := by
    dsimp only [d]
    rw [Finset.sum_comm]
    have he : ∀ a ∈ I, (∑ x ∈ R, if x ∈ T a then (1 : ℝ) else 0) = (m : ℝ) := by
      intro a ha
      rw [sum_membership_indicator R (T a) (hTR a ha),hsize a ha]
    rw [Finset.sum_congr rfl he]
    simp
  have henergy : (∑ x ∈ R, (d x)^2) = ∑ a ∈ I, ∑ b ∈ I, ((T a ∩ T b).card : ℝ) := by
    dsimp only [d]
    simp_rw [sq,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    have hind : ∀ x, (if x ∈ T a then (1 : ℝ) else 0)*(if x ∈ T b then (1 : ℝ) else 0) =
        if x ∈ T a ∩ T b then (1 : ℝ) else 0 := by
      intro x
      by_cases hx : x ∈ T a <;> by_cases hy : x ∈ T b <;> simp only [Finset.mem_inter,hx,hy,ite_true,ite_false,and_self,and_false,and_true,mul_zero,mul_one]
    simp_rw [hind]
    exact sum_membership_indicator R _ (Finset.inter_subset_left.trans (hTR a ha))
  let row := fun a => ∑ b ∈ I, ((T a ∩ T b).card : ℝ)
  obtain ⟨a,ha,hmax⟩ := I.exists_max_image row hI
  have hs : (∑ b ∈ I, row b) ≤ (I.card : ℝ)*row a := by
    calc
      _ ≤ ∑ _b ∈ I, row a := Finset.sum_le_sum hmax
      _ = _ := by simp
  have he : (∑ x ∈ R, d x)^2 ≤ (R.card : ℝ)*(∑ x ∈ R, (d x)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1 : ℝ)) d
  rw [htotal,henergy] at he
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) R.card)
  have hIc : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  refine ⟨a,ha,?_⟩
  dsimp only [row] at hh
  nlinarith
end FiniteAlmostPeriods
end DirectedCycles
