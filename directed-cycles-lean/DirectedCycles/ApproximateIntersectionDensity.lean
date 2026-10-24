import DirectedCycles.FiniteAlmostPeriods
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

theorem card_difference_fiber (A B : Finset G) (x : G) :
    ({p ∈ A ×ˢ B | p.1⁻¹*p.2=x}).card = (B ∩ rightTranslate A x).card := by
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_inter.mpr ⟨hp2,Finset.mem_image.mpr ⟨p.1,hp1,by rw [← he]; simp⟩⟩
  · intro p hp q hq he
    have hpx := (Finset.mem_filter.mp hp).2
    have hqx := (Finset.mem_filter.mp hq).2
    apply Prod.ext _ he
    have hi : p.1⁻¹ = q.1⁻¹ := mul_right_cancel (by
      rw [he] at hpx
      exact hpx.trans hqx.symm)
    exact inv_injective hi
  · intro y hy
    obtain ⟨hyB,hyA⟩ := Finset.mem_inter.mp hy
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hyA
    refine ⟨(a,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hyB⟩,?_⟩,rfl⟩
    rw [← hax]
    simp

theorem difference_inter_translate_subset (A B : Finset G) (x : G) :
    ((B ∩ rightTranslate A x : Finset G) : Set G) /
      ((B ∩ rightTranslate A x : Finset G) : Set G) ⊆
      ((A : Set G)/(A : Set G)) ∩ ((B : Set G)/(B : Set G)) := by
  intro g hg
  obtain ⟨y,hy,z,hz,rfl⟩ := hg
  obtain ⟨hyB,hyA⟩ := Finset.mem_inter.mp hy
  obtain ⟨hzB,hzA⟩ := Finset.mem_inter.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hyA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hzA
  refine ⟨?_,⟨a*x,hyB,b*x,hzB,rfl⟩⟩
  refine ⟨a,ha,b,hb,?_⟩
  simp [div_eq_mul_inv,mul_assoc]

/-- The finite global density-intersection lemma, using the actual fibers
of (a,b) ↦ a^{-1}b and preserving the noncommutative product order. -/
theorem approximate_intersection_density (A A₁ A₂ : Finset G) (K δ₁ δ₂ : ℝ)
    (hA : IsApproximateSubgroup K (A : Set G))
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (h₁ : A₁ ⊆ A) (h₂ : A₂ ⊆ A)
    (hc₁ : δ₁*A.card ≤ A₁.card) (hc₂ : δ₂*A.card ≤ A₂.card) :
    ∃ B : Finset G, B ⊆ A ∧ (δ₁*δ₂/K)*A.card ≤ B.card ∧
      ((B : Set G)/(B : Set G)) ⊆
        ((A₁ : Set G)/(A₁ : Set G)) ∩ ((A₂ : Set G)/(A₂ : Set G)) := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hA.one_le
  have hKne := ne_of_gt hK
  have hA0 : (0 : ℝ) < A.card := by
    exact_mod_cast (show A.Nonempty from ⟨1,hA.one_mem⟩).card_pos
  let d := (δ₁*δ₂/K)*A.card
  have hd : 0 ≤ d := by positivity
  have hAsymm : A⁻¹ = A := by
    apply Finset.coe_injective
    simpa only [Finset.coe_inv] using hA.inv_eq_self
  have hmap : ∀ p ∈ A₁ ×ˢ A₂, p.1⁻¹*p.2 ∈ A^2 := by
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
    rw [pow_two]
    apply Finset.mul_mem_mul _ (h₂ hp₂)
    have hh : p.1⁻¹ ∈ A⁻¹ := Finset.inv_mem_inv (h₁ hp₁)
    simpa only [hAsymm] using hh
  have hsize : (A^2).card • d ≤ ((A₁ ×ˢ A₂).card : ℝ) := by
    have hs : ((A^2).card : ℝ) ≤ K*A.card := by simpa using hA.card_pow_le (n := 2)
    have hh := mul_le_mul_of_nonneg_right hs hd
    have hprod := mul_le_mul hc₁ hc₂ (by positivity) (by positivity)
    have he : K*A.card*d = (δ₁*A.card)*(δ₂*A.card) := by
      dsimp [d]
      field_simp
    simpa only [nsmul_eq_mul,Finset.card_product,Nat.cast_mul] using hh.trans (he.le.trans hprod)
  obtain ⟨x,hx,hfiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap
    (show (A^2).Nonempty from ⟨1,Finset.one_mem_pow hA.one_mem⟩) hsize
  refine ⟨A₂ ∩ rightTranslate A₁ x,Finset.inter_subset_left.trans h₂,?_,
    difference_inter_translate_subset A₁ A₂ x⟩
  simpa only [card_difference_fiber] using hfiber

/-- Iteration of the two-set density lemma, retaining an actual common
difference set rather than just a lower bound for an abstract intersection. -/
theorem approximate_finite_intersection_density (A : Finset G) (K δ : ℝ)
    (hA : IsApproximateSubgroup K (A : Set G)) (hδ : 0 ≤ δ)
    (l : List (Finset G))
    (hsub : ∀ C ∈ l, C ⊆ A) (hcard : ∀ C ∈ l, δ*A.card ≤ C.card) :
    ∃ B : Finset G, B ⊆ A ∧ (δ/K)^l.length*A.card ≤ B.card ∧
      ∀ C ∈ l, ((B : Set G)/(B : Set G)) ⊆ ((C : Set G)/(C : Set G)) := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hA.one_le
  induction l with
  | nil => exact ⟨A,Finset.Subset.refl _,by simp,by simp⟩
  | cons C l ih =>
    obtain ⟨B,hBA,hB,hBl⟩ := ih
      (fun D hD => hsub D (List.mem_cons_of_mem C hD))
      (fun D hD => hcard D (List.mem_cons_of_mem C hD))
    obtain ⟨D,hDA,hD,hDB⟩ := approximate_intersection_density A B C K ((δ/K)^l.length) δ
      hA (by positivity) hδ hBA (hsub C (List.mem_cons_self)) hB (hcard C (List.mem_cons_self))
    refine ⟨D,hDA,?_,?_⟩
    · simpa only [List.length_cons,pow_succ,mul_div_assoc] using hD
    · intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · exact fun x hx => (hDB hx).2
      · exact fun x hx => hBl E hE (hDB hx).1

end FiniteAlmostPeriods
end DirectedCycles
