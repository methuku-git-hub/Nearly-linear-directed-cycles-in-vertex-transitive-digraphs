module

public import DirectedCycles.DenseGrid
public import DirectedCycles.BinomialGrid
public import DirectedCycles.IntegerGram
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Matrix
namespace DirectedCycles

noncomputable def binomialCombination {n D : ℕ} (c : (Fin n → Fin D) → ℚ) :
    MvPolynomial (Fin n) ℚ :=
  ∑ a, MvPolynomial.C (c a) * binomialTensor (fun i => (a i).val)

theorem binomialCombination_eval {n D : ℕ} (c : (Fin n → Fin D) → ℚ)
    (t : Fin n → ℕ) :
    MvPolynomial.eval (fun i => (t i : ℚ)) (binomialCombination c) =
      ∑ a, (∏ i, ((t i).choose (a i).val : ℚ)) * c a := by
  simp only [binomialCombination,map_sum,map_mul,MvPolynomial.eval_C,binomialTensor_eval]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem binomialCombination_degree {n D : ℕ} (c : (Fin n → Fin D) → ℚ) :
    (binomialCombination c).totalDegree ≤ n * (D-1) := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.totalDegree_C,zero_add]
  refine (binomialTensor_degree _).trans ?_
  calc
    ∑ i, (a i).val ≤ ∑ _i : Fin n, (D-1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_sub_one_of_lt (a i).isLt
    _ = n * (D-1) := by simp

theorem binomialCombination_eq_zero_iff {n D : ℕ} (c : (Fin n → Fin D) → ℚ) :
    binomialCombination c = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply binomial_box_independent
    intro a
    have he := congrArg (MvPolynomial.eval (fun i => ((a i).val : ℚ))) h
    simpa only [binomialCombination_eval,map_zero] using he
  · intro h
    simp [binomialCombination,h]

/-- On a sufficiently dense subset of an integer box, tensor binomial
polynomials have injective evaluation. -/
theorem dense_binomial_zero {n D L : ℕ} (F : Finset (Fin n → ℕ))
    (hF : ∀ t ∈ F, ∀ i, t i < L)
    (hlarge : ((n * (D-1) : ℕ) : ℚ≥0) / L < (F.card : ℚ≥0) / (L : ℚ≥0)^n)
    (c : (Fin n → Fin D) → ℚ)
    (hz : ∀ t ∈ F, ∑ a, (∏ i, ((t i).choose (a i).val : ℚ)) * c a = 0) : c = 0 := by
  classical
  let castPoint : (Fin n → ℕ) → (Fin n → ℚ) := fun t i => t i
  have hi : Function.Injective castPoint := by
    intro a b h
    funext i
    have he : (a i : ℚ) = (b i : ℚ) := congrFun h i
    exact_mod_cast he
  let S : Finset ℚ := (Finset.range L).image (fun k : ℕ => (k : ℚ))
  let Fq : Finset (Fin n → ℚ) := F.image castPoint
  have hScard : S.card = L := by
    change ((Finset.range L).image (fun k : ℕ => (k : ℚ))).card = L
    rw [Finset.card_image_of_injective _ Nat.cast_injective,Finset.card_range]
  have hFcard : Fq.card = F.card := Finset.card_image_of_injective _ hi
  have hsub : Fq ⊆ Fintype.piFinset (fun _ : Fin n => S) := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_image.mpr ⟨t i,Finset.mem_range.mpr (hF t ht i),rfl⟩
  apply (binomialCombination_eq_zero_iff c).mp
  apply dense_grid_polynomial_zero S Fq hsub (n*(D-1))
  · simpa only [hScard,hFcard] using hlarge
  · exact binomialCombination_degree c
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (binomialCombination_eval c t).trans (hz t ht)

noncomputable def integerBinomialMatrix {n : ℕ} (D : ℕ) (F : Finset (Fin n → ℕ)) :
    Matrix F (Fin n → Fin D) ℤ := fun t a => ∏ i, ((t.val i).choose (a i).val : ℤ)

theorem integerBinomialMatrix_injective {n D L : ℕ} (F : Finset (Fin n → ℕ))
    (hF : ∀ t ∈ F, ∀ i, t i < L)
    (hlarge : ((n * (D-1) : ℕ) : ℚ≥0) / L < (F.card : ℚ≥0) / (L : ℚ≥0)^n) :
    Function.Injective ((integerBinomialMatrix D F).map (Int.castRingHom ℚ)).mulVec := by
  change Function.Injective ((integerBinomialMatrix D F).map (Int.castRingHom ℚ)).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro c hc
  apply dense_binomial_zero F hF hlarge c
  intro t ht
  have he := congrFun hc (⟨t,ht⟩ : F)
  simpa [integerBinomialMatrix, Matrix.mulVec, dotProduct, Matrix.map_apply] using he

theorem integerBinomialMatrix_bound {n D L : ℕ} (hL : 0 < L)
    (F : Finset (Fin n → ℕ)) (hF : ∀ t ∈ F, ∀ i, t i < L) :
    ∀ t a, (integerBinomialMatrix D F t a).natAbs ≤ L^(n*(D-1)) := by
  intro t a
  simp only [integerBinomialMatrix,← Nat.cast_prod,Int.natAbs_natCast]
  calc
    ∏ i, (t.val i).choose (a i).val ≤ ∏ _i : Fin n, L^(D-1) := by
      apply Finset.prod_le_prod
      intro i _
      calc
        (t.val i).choose (a i).val ≤ (t.val i)^(a i).val := Nat.choose_le_pow _ _
        _ ≤ L^(a i).val := Nat.pow_le_pow_left (hF t.val t.property i).le _
        _ ≤ L^(D-1) := Nat.pow_le_pow_right hL (Nat.le_sub_one_of_lt (a i).isLt)
    _ = L^(n*(D-1)) := by simp [← pow_mul,Nat.mul_comm]

/-- Dense integer evaluation yields an explicit multiplier for its coefficients,
with no torsion-free hypothesis on the target group. -/
theorem dense_binomial_multiplier {n D L : ℕ} (hL : 0 < L)
    (F : Finset (Fin n → ℕ)) (hF : ∀ t ∈ F, ∀ i, t i < L)
    (hlarge : ((n * (D-1) : ℕ) : ℚ≥0) / L < (F.card : ℚ≥0) / (L : ℚ≥0)^n)
    {V : Type*} [AddCommGroup V] (v : (Fin n → Fin D) → V) (W : AddSubgroup V)
    (h : ∀ t ∈ F, ∑ a, (∏ i, ((t i).choose (a i).val : ℤ)) • v a ∈ W) :
    ∃ M : ℕ, 0 < M ∧ M ≤ (D^n).factorial * L^((n+2*n*(D-1))*D^n) ∧
      ∀ a, M • v a ∈ W := by
  classical
  obtain ⟨M,hM,hbound,hspan⟩ := integer_gram_multiplier (integerBinomialMatrix D F)
    (integerBinomialMatrix_injective F hF hlarge) (L^(n*(D-1)))
    (integerBinomialMatrix_bound hL F hF) v W (fun t => h t.val t.property)
  have hcard : F.card ≤ L^n := by
    have hs : F ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) := by
      intro t ht
      exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (hF t ht i))
    simpa using Finset.card_le_card hs
  refine ⟨M,hM,hbound.trans ?_,hspan⟩
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
  calc
    (D^n).factorial * (F.card * (L^(n*(D-1)))^2)^(D^n) ≤
        (D^n).factorial * (L^n * (L^(n*(D-1)))^2)^(D^n) := by gcongr
    _ = (D^n).factorial * L^((n+2*n*(D-1))*D^n) := by
      simp only [← pow_mul,← pow_add]
      congr 3
      ring

end DirectedCycles
