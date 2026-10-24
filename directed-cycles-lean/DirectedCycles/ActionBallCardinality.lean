import DirectedCycles.ActionBalls
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

theorem actionStepSet_inv {G V : Type*} [Group G] [MulAction G V]
    (R : Digraph V) (e : V) (hs : ∀ x y, R x y → R y x)
    (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y) :
    (actionStepSet R e : Set G)⁻¹ = actionStepSet R e := by
  have h : ∀ g : G, g ∈ actionStepSet R e → g⁻¹ ∈ actionStepSet R e := by
    intro g hg
    rcases hg with hg | hg
    · left
      have hh := congrArg (fun z => g⁻¹ • z) hg
      simpa only [inv_smul_smul] using hh.symm
    · right
      have hh := (hR g⁻¹ (g • e) e).mpr (hs _ _ hg)
      simpa only [inv_smul_smul] using hh
  ext g
  change g⁻¹ ∈ actionStepSet R e ↔ g ∈ actionStepSet R e
  exact ⟨fun hg => by simpa only [inv_inv] using h g⁻¹ hg,h g⟩

/-- Every fibre of a transitive action has the size of a point stabilizer. -/
noncomputable def actionPreimageEquiv {G V : Type*} [Group G] [MulAction G V]
    (e : V) (ht : ∀ x y : V, ∃ g : G, g • x = y) (A : Set V) :
    {g : G // g • e ∈ A} ≃ A × MulAction.stabilizer G e := by
  classical
  choose t ht using ht e
  exact {
    toFun := fun g => ⟨⟨g.val • e,g.property⟩,
      ⟨(t (g.val • e))⁻¹*g.val,by
        change ((t (g.val • e))⁻¹*g.val) • e = e
        rw [mul_smul]
        exact (inv_smul_eq_iff).mpr (ht (g.val • e)).symm⟩⟩
    invFun := fun p => ⟨t p.1.val*p.2.val,by
      rw [mul_smul,p.2.property,ht]
      exact p.1.property⟩
    left_inv := by intro g; apply Subtype.ext; exact mul_inv_cancel_left _ _
    right_inv := by
      rintro ⟨⟨y,hy⟩,⟨h,hh⟩⟩
      have he : (t y*h) • e = y := by rw [mul_smul,hh,ht]
      apply Prod.ext
      · exact Subtype.ext he
      · apply Subtype.ext
        dsimp
        rw [he,inv_mul_cancel_left] }

theorem action_preimage_card {G V : Type*} [Group G] [MulAction G V]
    (e : V) (ht : ∀ x y : V, ∃ g : G, g • x = y) (A : Set V) :
    Nat.card {g : G // g • e ∈ A} = Nat.card A * Nat.card (MulAction.stabilizer G e) := by
  rw [Nat.card_congr (actionPreimageEquiv e ht A),Nat.card_prod]

theorem actionStepSet_pow_card {G V : Type*} [Group G] [MulAction G V]
    (R : Digraph V) (e : V) (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(actionStepSet R e ^ n : Set G) =
      Nat.card (relationBall R e n) * Nat.card (MulAction.stabilizer G e) := by
  rw [actionStepSet_pow R e hR ht n hn]
  exact action_preimage_card e ht _

/-- The standard small-tripling lemma, in the set cardinality interface
used by action balls. This is a wrapper around Mathlib's proved theorem. -/
theorem approximate_of_small_tripling {G : Type*} [Group G] [Finite G]
    (A : Set G) (K : ℝ) (h1 : 1 ∈ A) (hi : A⁻¹ = A)
    (hc : (Nat.card ↥(A^3) : ℝ) ≤ K * Nat.card A) :
    IsApproximateSubgroup (K^3) (A^2) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let F := A.toFinset
  have hF : (F : Set G) = A := Set.coe_toFinset A
  have hF1 : 1 ∈ F := by simpa only [← hF,Finset.mem_coe] using h1
  have hFi : F⁻¹ = F := by
    apply Finset.coe_injective
    simpa only [Finset.coe_inv,hF] using hi
  have hFc : ((F^3).card : ℝ) ≤ K * F.card := by
    have he1 : Nat.card A = F.card := by rw [← hF,Nat.card_coe_set_eq,Set.ncard_coe_finset]
    have he3 : Nat.card ↥(A^3) = (F^3).card := by
      rw [← hF,← Finset.coe_pow,Nat.card_coe_set_eq,Set.ncard_coe_finset]
    simpa only [he1,he3] using hc
  have hh := IsApproximateSubgroup.of_small_tripling hF1 hFi hFc
  simpa only [Finset.coe_pow,hF] using hh

theorem action_ball_approximate {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (R : Digraph V) (e : V) (hs : ∀ x y, R x y → R y x)
    (hR : ∀ g : G, ∀ x y, R (g • x) (g • y) ↔ R x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (m : ℕ) (hm : 1 ≤ m)
    (K : ℝ) (hc : (Nat.card (relationBall R e (3*m)) : ℝ) ≤
      K * Nat.card (relationBall R e m)) :
    IsApproximateSubgroup (K^3) ((actionStepSet R e : Set G) ^ (2*m)) := by
  have h1 : (1 : G) ∈ (actionStepSet R e : Set G)^m :=
    Set.one_mem_pow (actionStepSet_one R e)
  have hi : ((actionStepSet R e : Set G)^m)⁻¹ = actionStepSet R e ^ m := by
    rw [← inv_pow,actionStepSet_inv R e hs hR]
  have hh : (Nat.card ↥((actionStepSet R e : Set G)^(3*m)) : ℝ) ≤
      K * Nat.card ↥((actionStepSet R e : Set G)^m) := by
    rw [actionStepSet_pow_card R e hR ht (3*m) (by omega),
      actionStepSet_pow_card R e hR ht m hm]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Nat.card (MulAction.stabilizer G e)) : (0 : ℝ) ≤ _)]
  have hh' := approximate_of_small_tripling ((actionStepSet R e : Set G)^m) K h1 hi
    (by simpa only [← pow_mul,Nat.mul_comm m 3] using hh)
  simpa only [← pow_mul,Nat.mul_comm m 2] using hh'

end DirectedCycles
