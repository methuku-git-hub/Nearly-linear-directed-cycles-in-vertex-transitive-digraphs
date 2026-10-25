module

public import DirectedCycles.FiniteAlmostPeriods
public import Mathlib.Combinatorics.Additive.Energy

@[expose] public section

set_option autoImplicit false
open scoped Pointwise BigOperators
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

theorem card_equal_translate_pairs (B : Finset G) (a b : G) :
    ({p ∈ B ×ˢ B | p.1*a = p.2*b}).card =
      (rightTranslate B a ∩ rightTranslate B b).card := by
  apply Finset.card_bij (fun p _ => p.1*a)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨p.1,hp1,rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2,hp2,he.symm⟩
  · intro p hp q hq he
    have h1 : p.1 = q.1 := mul_right_cancel he
    have h2 : p.2 = q.2 := mul_right_cancel
      ((Finset.mem_filter.mp hp).2.symm.trans (he.trans (Finset.mem_filter.mp hq).2))
    exact Prod.ext h1 h2
  · intro x hx
    obtain ⟨hx1,hx2⟩ := Finset.mem_inter.mp hx
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp hx1
    obtain ⟨q,hq,hqb⟩ := Finset.mem_image.mp hx2
    exact ⟨(p,q),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hpa.trans hqb.symm⟩,hpa⟩

theorem mulEnergy_eq_sum_overlap (A B : Finset G) :
    Finset.mulEnergy B A = ∑ a ∈ A, ∑ b ∈ A,
      (rightTranslate B a ∩ rightTranslate B b).card := by
  rw [Finset.mulEnergy,Finset.card_filter,Finset.sum_product,Finset.sum_comm]
  simp_rw [← Finset.card_filter,card_equal_translate_pairs]
  exact Finset.sum_product _ _ _

/-- Cauchy--Schwarz gives an inequality, without an equality assumption
on the multiplicities of products. -/
theorem exists_large_overlap_row (A B : Finset G) (hA : A.Nonempty) :
    ∃ a ∈ A, A.card * B.card^2 ≤
      (B*A).card * (∑ b ∈ A, (rightTranslate B a ∩ rightTranslate B b).card) := by
  let row := fun a => ∑ b ∈ A, (rightTranslate B a ∩ rightTranslate B b).card
  obtain ⟨a,ha,hmax⟩ := A.exists_max_image row hA
  have hs : Finset.mulEnergy B A ≤ A.card * row a := by
    rw [mulEnergy_eq_sum_overlap]
    exact (Finset.sum_le_sum hmax).trans_eq (by simp [row])
  have he := Finset.le_card_mul_mul_mulEnergy B A
  have hh := he.trans (Nat.mul_le_mul_left (B*A).card hs)
  refine ⟨a,ha,?_⟩
  apply (Nat.mul_le_mul_left_iff hA.card_pos).mp
  dsimp [row] at hh
  nlinarith

/-- A positive average forces many entries above half the average scale. -/
theorem many_large_values {α : Type*} [DecidableEq α] (A : Finset α) (f : α → ℝ)
    (M δ : ℝ) (hM : 0 < M) (hδ : 0 ≤ δ)
    (hf : ∀ a ∈ A, f a ≤ M)
    (hs : 2*δ*A.card*M ≤ ∑ a ∈ A, f a) :
    δ*A.card ≤ ({a ∈ A | δ*M ≤ f a}).card := by
  let C := {a ∈ A | δ*M ≤ f a}
  have hp : ∀ a ∈ A, f a ≤ (if δ*M ≤ f a then M else 0) + δ*M := by
    intro a ha
    split_ifs with h
    · linarith [hf a ha,mul_nonneg hδ hM.le]
    · linarith
  have he : (∑ a ∈ A, ((if δ*M ≤ f a then M else 0)+δ*M)) =
      (C.card : ℝ)*M+A.card*(δ*M) := by
    rw [Finset.sum_add_distrib,← Finset.sum_filter]
    simp [C]
  have hh := (Finset.sum_le_sum hp).trans_eq he
  nlinarith

theorem many_overlapping_translates (A B : Finset G) (K t δ : ℝ)
    (hA : A.Nonempty) (hBA : B ⊆ A) (hK : 0 < K) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hB : t*A.card ≤ B.card) (hprod : ((B*A).card : ℝ) ≤ K*A.card)
    (hscale : 2*δ*K ≤ t^2) :
    ∃ a ∈ A, δ*A.card ≤ ({b ∈ A |
      δ*A.card ≤ ((rightTranslate B a ∩ rightTranslate B b).card : ℝ)}).card := by
  obtain ⟨a,ha,hrow⟩ := exists_large_overlap_row A B hA
  let row : ℝ := ∑ b ∈ A, ((rightTranslate B a ∩ rightTranslate B b).card : ℝ)
  have hrow0 : 0 ≤ row := Finset.sum_nonneg (by intros; positivity)
  have hcA : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have he : (A.card : ℝ) * B.card^2 ≤ (B*A).card * row := by
    dsimp [row]
    exact_mod_cast hrow
  have he' : (B.card : ℝ)^2 ≤ K*row := by
    have hh := mul_le_mul_of_nonneg_right hprod hrow0
    nlinarith
  have hlow : (t*A.card)^2 ≤ (B.card : ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hB
  have hsc := mul_le_mul_of_nonneg_right hscale (sq_nonneg (A.card : ℝ))
  have hs : 2*δ*A.card*(A.card : ℝ) ≤ row := by
    nlinarith
  refine ⟨a,ha,many_large_values A
    (fun b => ((rightTranslate B a ∩ rightTranslate B b).card : ℝ))
    A.card δ hcA hδ ?_ hs⟩
  intro b hb
  have hh : (rightTranslate B a ∩ rightTranslate B b).card ≤ A.card :=
    (Finset.card_le_card Finset.inter_subset_left).trans
      ((card_rightTranslate B a).le.trans (Finset.card_le_card hBA))
  exact_mod_cast hh

end FiniteAlmostPeriods
end DirectedCycles
