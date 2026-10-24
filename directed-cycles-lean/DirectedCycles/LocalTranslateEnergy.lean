import DirectedCycles.FiniteFamilyOverlap
import DirectedCycles.LocalFiniteRightTranslate
import DirectedCycles.LocalFiniteProductCard

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem mem_finsetMul (A B : Finset G) (x : G) :
    x ∈ L.finsetMul A B ↔ ∃ a ∈ A, ∃ b ∈ B, L.mulRel a b x := by
  classical
  exact Set.mem_toFinset

theorem finsetMul_card_le_doubling {K : ℕ} {A B : Finset G}
    (hA : IsLocalFiniteApproximateGroup L K A) (hBA : B ⊆ A) :
    (L.finsetMul B A).card ≤ K*A.card := by
  classical
  let R := (L.wordPower (A : Set G) 2).toFinset
  have hsub : L.finsetMul B A ⊆ R := by
    intro x hx
    obtain ⟨b,hb,a,ha,hm⟩ := (L.mem_finsetMul B A x).1 hx
    apply Set.mem_toFinset.mpr
    exact ⟨[b,a],rfl,by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl
      · exact hBA hb
      · exact ha,(Product.pair_iff L _ _ _).2 hm⟩
  have hcard : R.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  exact (Finset.card_le_card hsub).trans (by rw [hcard]; exact local_approximate_doubling hA)

/-- Many overlapping right translates in a local approximate group. All
translations are actual injections with their multiplication domains proved;
the energy estimate is the pure finite-family Cauchy--Schwarz theorem. -/
theorem many_overlapping_right_translates [DecidableEq G] (hc : L.Cancellative)
    {K : ℕ} {A B : Finset G} (hA : IsLocalFiniteApproximateGroup L K A)
    (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hBA : B ⊆ A)
    (hB : t*A.card ≤ B.card) (hscale : 2*δ*(K : ℝ) ≤ t^2) :
    ∃ a ∈ A, δ*A.card ≤ ({b ∈ A |
      δ*A.card ≤ ((L.rightTranslate B a ∩ L.rightTranslate B b).card : ℝ)}).card := by
  classical
  let R := L.finsetMul B A
  have hnon : A.Nonempty := ⟨L.one,hA.one_mem⟩
  have hdom : ∀ a ∈ A, ∀ b ∈ B, L.Defined b a := by
    intro a ha b hb
    obtain ⟨x,hx⟩ := hA.allProducts [b,a] (by simp) (by aesop)
    exact ⟨x,(Product.pair_iff L _ _ _).1 hx⟩
  have hTR : ∀ a ∈ A, L.rightTranslate B a ⊆ R := by
    intro a ha x hx
    obtain ⟨b,hb,hm⟩ := (L.mem_rightTranslate B a x).1 hx
    exact (L.mem_finsetMul B A x).2 ⟨b,hb,a,ha,hm⟩
  obtain ⟨a,ha,hrow⟩ := FiniteAlmostPeriods.finite_family_overlap_row A R (L.rightTranslate B) B.card hnon hTR
    (fun a ha => L.card_rightTranslate hc B a (hdom a ha))
  let row : ℝ := ∑ b ∈ A, ((L.rightTranslate B a ∩ L.rightTranslate B b).card : ℝ)
  have hrow0 : 0 ≤ row := Finset.sum_nonneg (by intros; positivity)
  have hcA : (0 : ℝ) < A.card := by exact_mod_cast hnon.card_pos
  have hK : 0 < (K : ℝ) := by exact_mod_cast hA.one_le
  have hprod : (R.card : ℝ) ≤ (K : ℝ)*A.card := by exact_mod_cast L.finsetMul_card_le_doubling hA hBA
  have he' : (B.card : ℝ)^2 ≤ (K : ℝ)*row := by
    have hh := mul_le_mul_of_nonneg_right hprod hrow0
    change (A.card : ℝ)*(B.card : ℝ)^2 ≤ R.card*row at hrow
    nlinarith
  have hlow : (t*A.card)^2 ≤ (B.card : ℝ)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hB
  have hsc := mul_le_mul_of_nonneg_right hscale (sq_nonneg (A.card : ℝ))
  have hs : 2*δ*A.card*(A.card : ℝ) ≤ row := by nlinarith
  refine ⟨a,ha,FiniteAlmostPeriods.many_large_values A
    (fun b => ((L.rightTranslate B a ∩ L.rightTranslate B b).card : ℝ)) A.card δ hcA hδ ?_ hs⟩
  intro b _
  have hh : (L.rightTranslate B a ∩ L.rightTranslate B b).card ≤ A.card :=
    (Finset.card_le_card Finset.inter_subset_left).trans
      ((L.card_rightTranslate hc B a (hdom a ha)).le.trans (Finset.card_le_card hBA))
  exact_mod_cast hh
end LocalGroupAlgebra
end DirectedCycles
