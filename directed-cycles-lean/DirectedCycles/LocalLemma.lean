module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
Finite asymmetric local lemma, reused from the earlier undirected formalization.
This proves the abstract finite probability theorem only. Its application to
sampled directed paths in manuscript Lemma 4.5 is a separate open obligation.
-/

namespace DirectedCycles

open Finset

attribute [local instance] Classical.propDecidable

section AbstractAvoidance

variable {I : Type*} [DecidableEq I]

private theorem product_le_one_real (f : I → ℝ) (s : Finset I)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    (∏ i ∈ s, f i) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hn := Finset.prod_nonneg (fun j (_ : j ∈ s) => h0 j)
      nlinarith [h0 i, h1 i]

private theorem product_antitone (f : I → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1)
    {s t : Finset I} (hst : s ⊆ t) :
    (∏ i ∈ t, f i) ≤ ∏ i ∈ s, f i := by
  have hprod := Finset.prod_sdiff hst (f := f)
  have hsmall := product_le_one_real f (t \ s) h0 h1
  have hn := Finset.prod_nonneg (fun j (_ : j ∈ s) => h0 j)
  nlinarith

/-- Multiply the individual avoidance bounds along a finite sequence. -/
private theorem avoidance_chain (p : Finset I → ℝ) (x : I → ℝ)
    (hx : ∀ i, x i < 1) (U : Finset I)
    (hstep : ∀ K ⊆ U, ∀ i ∈ U, i ∉ K →
      (1 - x i) * p K ≤ p (insert i K))
    (S T : Finset I) (hdisj : Disjoint S T) (hST : S ∪ T ⊆ U) :
    (∏ i ∈ S, (1 - x i)) * p T ≤ p (S ∪ T) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hiT : i ∉ T := by simpa using (Finset.disjoint_insert_left.mp hdisj).1
      have hdisj' := (Finset.disjoint_insert_left.mp hdisj).2
      have hST' : S ∪ T ⊆ U := by
        intro j hj
        apply hST
        simp only [Finset.mem_union, Finset.mem_insert] at hj ⊢
        tauto
      have hbase := ih hdisj' hST'
      have hiU : i ∈ U := hST (by simp)
      have h := hstep (S ∪ T) hST' i hiU (by simp [hi, hiT])
      have hm := mul_le_mul_of_nonneg_left hbase (le_of_lt (sub_pos.mpr (hx i)))
      rw [Finset.prod_insert hi, Finset.insert_union]
      nlinarith

/-- Local lemma for abstract avoidance probabilities satisfying the elementary
probability identities. The next section proves those identities for actual
finite probability spaces. -/
theorem abstract_local_lemma (p : Finset I → ℝ) (N : I → Finset I) (x : I → ℝ)
    (pempty : p ∅ = 1) (pnonneg : ∀ J, 0 ≤ p J)
    (bad_mono : ∀ i J K, K ⊆ J →
      p J - p (insert i J) ≤ p K - p (insert i K))
    (independent : ∀ i J, i ∉ J → Disjoint J (N i) →
      p J - p (insert i J) = (1 - p {i}) * p J)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, 1 - p {i} ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∀ J, 0 < p J := by
  have hfactor0 (i : I) : 0 ≤ 1 - x i := le_of_lt (sub_pos.mpr (hx1 i))
  have hfactor1 (i : I) : 1 - x i ≤ 1 := by linarith [hx0 i]
  have hstep : ∀ J : Finset I, ∀ i, i ∉ J →
      (1 - x i) * p J ≤ p (insert i J) := by
    intro J
    refine Finset.strongInductionOn J ?_
    intro J ih i hi
    let S := J ∩ N i
    let T := J \ N i
    have hST : S ∪ T = J := by ext j; simp [S, T]; tauto
    have hdisj : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro j hjS hjT
      simp only [S, T, Finset.mem_inter, Finset.mem_sdiff] at hjS hjT
      exact hjT.2 hjS.2
    have hlocal : ∀ K ⊆ J, ∀ j ∈ J, j ∉ K →
        (1 - x j) * p K ≤ p (insert j K) := by
      intro K hK j hj hjK
      have hproper : K ⊂ J := Finset.ssubset_iff_subset_ne.mpr
        ⟨hK, fun heq => hjK (heq.symm ▸ hj)⟩
      exact ih K hproper j hjK
    have hchain := avoidance_chain p x hx1 J hlocal S T hdisj
      (by rw [hST])
    rw [hST] at hchain
    have hTsub : T ⊆ J := Finset.sdiff_subset
    have hiT : i ∉ T := fun h => hi (hTsub h)
    have hTN : Disjoint T (N i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hNj
      exact (Finset.mem_sdiff.mp hj).2 hNj
    have hind := independent i T hiT hTN
    have hmono := bad_mono i J T hTsub
    have hprod : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ S, (1 - x j) :=
      product_antitone (fun j => 1 - x j) hfactor0 hfactor1 Finset.inter_subset_right
    have hpi : 1 - p {i} ≤ x i * ∏ j ∈ S, (1 - x j) :=
      (hLLL i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    have hmul := mul_le_mul_of_nonneg_right hpi (pnonneg T)
    have hmul2 := mul_le_mul_of_nonneg_left hchain (hx0 i)
    nlinarith
  intro J
  induction J using Finset.induction_on with
  | empty => rw [pempty]; norm_num
  | @insert i J hi ih =>
      exact lt_of_lt_of_le (mul_pos (sub_pos.mpr (hx1 i)) ih) (hstep J i hi)

end AbstractAvoidance

section FiniteProbability

variable {Ω I : Type*} [Fintype Ω] [DecidableEq I]

/-- Avoid all bad events indexed by `J`. -/
def Avoids (A : I → Ω → Prop) (J : Finset I) (ω : Ω) : Prop :=
  ∀ i ∈ J, ¬ A i ω

noncomputable def avoidProbability (w : Ω → ℝ) (A : I → Ω → Prop)
    (J : Finset I) : ℝ := by
  classical
  exact ∑ ω, if Avoids A J ω then w ω else 0

omit [DecidableEq I] in
private theorem avoidProbability_empty (w : Ω → ℝ) (A : I → Ω → Prop)
    (hw : ∑ ω, w ω = 1) : avoidProbability w A ∅ = 1 := by
  classical
  simpa [avoidProbability, Avoids] using hw

omit [DecidableEq I] in
private theorem avoidProbability_nonneg (w : Ω → ℝ) (A : I → Ω → Prop)
    (hw : ∀ ω, 0 ≤ w ω) (J : Finset I) : 0 ≤ avoidProbability w A J := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

private theorem avoidance_difference (w : Ω → ℝ) (A : I → Ω → Prop)
    (i : I) (J : Finset I) :
    avoidProbability w A J - avoidProbability w A (insert i J) =
      ∑ ω, if A i ω ∧ Avoids A J ω then w ω else 0 := by
  classical
  unfold avoidProbability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  have h : Avoids A (insert i J) ω ↔ ¬ A i ω ∧ Avoids A J ω := by
    simp [Avoids]
  by_cases ha : A i ω <;> by_cases hj : Avoids A J ω <;> simp [h, ha, hj]

private theorem avoidance_bad_mono (w : Ω → ℝ) (A : I → Ω → Prop)
    (hw : ∀ ω, 0 ≤ w ω) (i : I) (J K : Finset I) (hKJ : K ⊆ J) :
    avoidProbability w A J - avoidProbability w A (insert i J) ≤
      avoidProbability w A K - avoidProbability w A (insert i K) := by
  classical
  rw [avoidance_difference, avoidance_difference]
  apply Finset.sum_le_sum
  intro ω _
  have himp : Avoids A J ω → Avoids A K ω :=
    fun hj k hk => hj k (hKJ hk)
  by_cases ha : A i ω <;> by_cases hj : Avoids A J ω <;>
    by_cases hk : Avoids A K ω <;> simp_all

/-- **Asymmetric local lemma for a finite probability space.**
Here `1 - avoidProbability w A {i}` is exactly the probability of `A i`.
The `independent` premise expresses independence from avoidance of an
arbitrary collection of non-neighbors. No finiteness of all of `I` is needed,
since the conclusion is for each finite `J`.
-/
theorem finite_asymmetric_local_lemma
    (w : Ω → ℝ) (A : I → Ω → Prop) (N : I → Finset I) (x : I → ℝ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (independent : ∀ i J, i ∉ J → Disjoint J (N i) →
      avoidProbability w A J - avoidProbability w A (insert i J) =
        (1 - avoidProbability w A {i}) * avoidProbability w A J)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, 1 - avoidProbability w A {i} ≤
      x i * ∏ j ∈ N i, (1 - x j)) (J : Finset I) :
    0 < avoidProbability w A J :=
  abstract_local_lemma (avoidProbability w A) N x
    (avoidProbability_empty w A hw1) (avoidProbability_nonneg w A hw0)
    (avoidance_bad_mono w A hw0) independent hx0 hx1 hLLL J

omit [DecidableEq I] in
/-- Positive avoidance probability gives an actual outcome avoiding all the
specified bad events. This includes outcome spaces with zero-weight points. -/
theorem exists_avoiding_outcome_of_positive (w : Ω → ℝ) (A : I → Ω → Prop)
    (J : Finset I) (h : 0 < avoidProbability w A J) :
    ∃ ω : Ω, Avoids A J ω := by
  classical
  by_contra hn
  push Not at hn
  have hz : avoidProbability w A J = 0 := by
    simp [avoidProbability, hn]
  linarith

/-- The elementary product bound used in the large-orbit application. -/
theorem one_sub_sum_le_product (x : I → ℝ) (S : Finset I)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    1 - (∑ i ∈ S, x i) ≤ ∏ i ∈ S, (1 - x i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hs := Finset.sum_nonneg (fun j (_ : j ∈ S) => hx0 j)
      have hp := Finset.prod_nonneg (fun j (_ : j ∈ S) => sub_nonneg.mpr (hx1 j))
      have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx1 i))
      nlinarith [hx0 i]

/-- The choice `x_i = 2 p_i` is valid when every probability is at most 1/48
and the sum over each dependency neighborhood is at most 1/4. These are the
bounds established in the draft's application (indeed its sum is <= 1/8).
This is an arithmetic implication, not a claim about the route experiment. -/
theorem local_lemma_weight_condition (p : I → ℝ) (N : I → Finset I)
    (hp0 : ∀ i, 0 ≤ p i) (hsmall : ∀ i, p i ≤ 1 / 48)
    (hsum : ∀ i, (∑ j ∈ N i, p j) ≤ 1 / 4) :
    (∀ i, 0 ≤ 2 * p i ∧ 2 * p i < 1) ∧
      ∀ i, p i ≤ (2 * p i) * ∏ j ∈ N i, (1 - 2 * p j) := by
  have hx0 (i : I) : 0 ≤ 2 * p i := mul_nonneg (by norm_num) (hp0 i)
  have hx1 (i : I) : 2 * p i ≤ 1 := by linarith [hsmall i]
  constructor
  · intro i
    exact ⟨hx0 i, by linarith [hsmall i]⟩
  · intro i
    have hprod := one_sub_sum_le_product (fun j => 2 * p j) (N i) hx0 hx1
    rw [← Finset.mul_sum] at hprod
    have hs := hsum i
    have hm := mul_le_mul_of_nonneg_left hprod (hx0 i)
    nlinarith [hp0 i]

end FiniteProbability


end DirectedCycles
