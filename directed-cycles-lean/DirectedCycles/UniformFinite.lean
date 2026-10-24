import DirectedCycles.LocalLemma
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Averaging on the actual finite uniform probability space. -/
noncomputable def uniformAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

noncomputable def eventIndicator (P : Prop) : ℝ := if P then 1 else 0

theorem eventIndicator_nonneg (P : Prop) : 0 ≤ eventIndicator P := by
  unfold eventIndicator; split_ifs <;> norm_num

theorem eventIndicator_le_one (P : Prop) : eventIndicator P ≤ 1 := by
  unfold eventIndicator; split_ifs <;> norm_num

theorem eventIndicator_not (P : Prop) : eventIndicator (¬ P) = 1 - eventIndicator P := by
  by_cases h : P <;> simp [eventIndicator, h]

theorem eventIndicator_and (P Q : Prop) : eventIndicator (P ∧ Q) = eventIndicator P * eventIndicator Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [eventIndicator, hP, hQ]

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] (A : Ω → Prop) : ℝ :=
  uniformAverage (fun ω => eventIndicator (A ω))

theorem uniformAverage_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ uniformAverage f :=
  div_nonneg (Finset.sum_nonneg (fun ω _ => hf ω)) (Nat.cast_nonneg _)

theorem uniformAverage_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : uniformAverage f ≤ uniformAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem uniformAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformAverage (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [uniformAverage, h]

theorem uniformAverage_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformAverage (fun ω => f ω + g ω) = uniformAverage f + uniformAverage g := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformAverage (fun ω => f ω - g ω) = uniformAverage f - uniformAverage g := by
  simp [uniformAverage, Finset.sum_sub_distrib, sub_div]

theorem uniformAverage_sum {Ω I : Type*} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    uniformAverage (fun ω => ∑ i, f i ω) = ∑ i, uniformAverage (f i) := by
  simp only [uniformAverage, Finset.sum_div]
  exact Finset.sum_comm

theorem uniformAverage_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (f : Λ → ℝ) : uniformAverage (fun ω => f (e ω)) = uniformAverage f := by
  unfold uniformAverage
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

theorem uniformAverage_prod_mul {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (f : Ω → ℝ) (g : Λ → ℝ) :
    uniformAverage (fun p : Ω × Λ => f p.1 * g p.2) = uniformAverage f * uniformAverage g := by
  simp only [uniformAverage, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul,
    Fintype.card_prod, Nat.cast_mul]
  ring

theorem uniformAverage_prod_left {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Λ]
    (f : Ω → ℝ) : uniformAverage (fun p : Ω × Λ => f p.1) = uniformAverage f := by
  simpa only [mul_one, uniformAverage_const] using uniformAverage_prod_mul f (fun _ : Λ => 1)

theorem uniformAverage_prod_right {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Ω]
    (g : Λ → ℝ) : uniformAverage (fun p : Ω × Λ => g p.2) = uniformAverage g := by
  simpa only [one_mul, uniformAverage_const] using uniformAverage_prod_mul (fun _ : Ω => 1) g

theorem uniformProbability_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    0 ≤ uniformProbability A := uniformAverage_nonneg _ (fun ω => eventIndicator_nonneg (A ω))

theorem uniformProbability_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Ω → Prop) :
    uniformProbability A ≤ 1 := by
  unfold uniformProbability
  calc uniformAverage (fun ω => eventIndicator (A ω)) ≤ uniformAverage (fun _ : Ω => 1) :=
         uniformAverage_mono (fun ω => eventIndicator_le_one (A ω))
       _ = 1 := uniformAverage_const 1

theorem uniformProbability_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Ω → Prop) :
    uniformProbability (fun ω => ¬ A ω) = 1 - uniformProbability A := by
  simp only [uniformProbability, eventIndicator_not, uniformAverage_sub, uniformAverage_const]

theorem uniformProbability_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (A : Λ → Prop) :
    uniformProbability (fun ω => A (e ω)) = uniformProbability A := by
  unfold uniformProbability
  exact uniformAverage_equiv e (fun ω => eventIndicator (A ω))

/-- Finite products of independent uniform choices: functions of disjoint
coordinate sets have factorizing averages. -/
def DependsOn {I : Type*} {β : I → Type*} {Y : Sort*}
    (S : Finset I) (f : (∀ i, β i) → Y) : Prop :=
  ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → f ω = f ω'

set_option maxHeartbeats 1000000 in
theorem uniformAverage_mul_of_disjoint_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (S T : Finset I) (hST : Disjoint S T) (f g : (∀ i, β i) → ℝ)
    (hf : DependsOn S f) (hg : DependsOn T g) :
    uniformAverage (fun ω => f ω * g ω) = uniformAverage f * uniformAverage g := by
  let L := ∀ i : {i // i ∈ S}, β i
  let R := ∀ i : {i // i ∉ S}, β i
  let e : (∀ i, β i) ≃ L × R := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) β
  let ω₀ : ∀ i, β i := fun i => Classical.choice (inferInstance : Nonempty (β i))
  let fS := fun u : ∀ i : {i // i ∈ S}, β i => f (e.symm (u, fun i => ω₀ i))
  let gC := fun v : ∀ i : {i // i ∉ S}, β i => g (e.symm (fun i => ω₀ i, v))
  have hf' : ∀ ω, f ω = fS (e ω).1 := by
    intro ω
    apply hf
    intro i hi
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hg' : ∀ ω, g ω = gC (e ω).2 := by
    intro ω
    apply hg
    intro i hi
    have hiS : i ∉ S := fun hs => Finset.disjoint_left.mp hST hs hi
    simp [e, Equiv.piEquivPiSubtypeProd, hiS]
  have hff : uniformAverage f = uniformAverage fS := by
    calc uniformAverage f = uniformAverage (fun ω => fS (e ω).1) := by
           congr 1; funext ω; exact hf' ω
         _ = uniformAverage (fun p : L × R => fS p.1) := uniformAverage_equiv e (fun p : L × R => fS p.1)
         _ = uniformAverage fS := uniformAverage_prod_left _
  have hgg : uniformAverage g = uniformAverage gC := by
    calc uniformAverage g = uniformAverage (fun ω => gC (e ω).2) := by
           congr 1; funext ω; exact hg' ω
         _ = uniformAverage (fun p : L × R => gC p.2) := uniformAverage_equiv e (fun p : L × R => gC p.2)
         _ = uniformAverage gC := uniformAverage_prod_right _
  rw [hff, hgg]
  calc uniformAverage (fun ω => f ω * g ω) =
      uniformAverage (fun ω => fS (e ω).1 * gC (e ω).2) := by
        congr 1; funext ω; rw [hf', hg']
    _ = uniformAverage (fun p : L × R => fS p.1 * gC p.2) := uniformAverage_equiv e (fun p : L × R => fS p.1 * gC p.2)
    _ = uniformAverage fS * uniformAverage gC := uniformAverage_prod_mul _ _

theorem uniformProbability_independent_of_disjoint_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (S T : Finset I) (hST : Disjoint S T) (A B : (∀ i, β i) → Prop)
    (hA : DependsOn S A) (hB : DependsOn T B) :
    uniformProbability (fun ω => A ω ∧ B ω) = uniformProbability A * uniformProbability B := by
  have hf : DependsOn S (fun ω => eventIndicator (A ω)) := by
    intro ω ω' he
    exact congrArg eventIndicator (hA ω ω' he)
  have hg : DependsOn T (fun ω => eventIndicator (B ω)) := by
    intro ω ω' he
    exact congrArg eventIndicator (hB ω ω' he)
  unfold uniformProbability
  simp only [eventIndicator_and]
  exact uniformAverage_mul_of_disjoint_coordinates β S T hST _ _ hf hg


/-- Uniform probabilities are exactly the weighted finite probabilities used
by the previously proved local lemma. -/
theorem uniform_avoidProbability {Ω J : Type*} [Fintype Ω]
    (A : J → Ω → Prop) (U : Finset J) :
    avoidProbability (fun _ : Ω => 1 / (Fintype.card Ω : ℝ)) A U =
      uniformProbability (Avoids A U) := by
  unfold avoidProbability uniformProbability uniformAverage
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : Avoids A U ω <;> simp [eventIndicator, h]

theorem uniform_avoid_difference {Ω J : Type*} [Fintype Ω] [DecidableEq J]
    (A : J → Ω → Prop) (i : J) (U : Finset J) :
    uniformProbability (Avoids A U) - uniformProbability (Avoids A (insert i U)) =
      uniformProbability (fun ω => A i ω ∧ Avoids A U ω) := by
  unfold uniformProbability
  rw [← uniformAverage_sub]
  congr 1
  funext ω
  have he : Avoids A (insert i U) ω ↔ ¬ A i ω ∧ Avoids A U ω := by simp [Avoids]
  by_cases ha : A i ω <;> by_cases hu : Avoids A U ω <;> simp [eventIndicator, he, ha, hu]

theorem uniform_avoid_singleton {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (A : J → Ω → Prop) (i : J) :
    1 - uniformProbability (Avoids A {i}) = uniformProbability (A i) := by
  have he : Avoids A {i} = fun ω => ¬ A i ω := by funext ω; simp [Avoids]
  rw [he, uniformProbability_compl]
  ring

/-- Avoiding any collection of coordinate-supported events depends only on
the union of their supports. -/
theorem dependsOn_avoidance {I J : Type*} [DecidableEq I] {β : I → Type*}
    (A : J → (∀ i, β i) → Prop) (S : J → Finset I)
    (hA : ∀ j, DependsOn (S j) (A j)) (U : Finset J) :
    DependsOn (U.biUnion S) (Avoids A U) := by
  intro ω ω' he
  apply propext
  have hevent : ∀ j ∈ U, A j ω = A j ω' := by
    intro j hj
    exact hA j ω ω' (fun i hi => he i (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩))
  constructor
  · intro h j hj
    rw [← hevent j hj]
    exact h j hj
  · intro h j hj
    rw [hevent j hj]
    exact h j hj

/-- A complete local-lemma application for independent finite coordinate
choices. All independence premises are derived from disjoint support sets. -/
theorem finite_coordinate_local_lemma {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (A : J → (∀ i, β i) → Prop) (S : J → Finset I) (N : J → Finset J)
    (hA : ∀ j, DependsOn (S j) (A j))
    (hN : ∀ j k, j ≠ k → k ∉ N j → Disjoint (S j) (S k))
    (p : J → ℝ) (hp : ∀ j, uniformProbability (A j) ≤ p j)
    (hp0 : ∀ j, 0 ≤ p j) (hsmall : ∀ j, p j ≤ 1 / 48)
    (hsum : ∀ j, (∑ k ∈ N j, p k) ≤ 1 / 4) :
    ∃ ω, ∀ j, ¬ A j ω := by
  let Ω := ∀ i, β i
  let w : Ω → ℝ := fun _ => 1 / (Fintype.card Ω : ℝ)
  have hw0 : ∀ ω, 0 ≤ w ω := fun _ => by dsimp [w]; positivity
  have hw1 : ∑ ω, w ω = 1 := by
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [w, hcard]
  have hind : ∀ j U, j ∉ U → Disjoint U (N j) →
      avoidProbability w A U - avoidProbability w A (insert j U) =
        (1 - avoidProbability w A {j}) * avoidProbability w A U := by
    intro j U hj hUN
    have hdis : Disjoint (S j) (U.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro i hi hU
      obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hU
      have hjk : j ≠ k := fun he => hj (he.symm ▸ hk)
      have hkN : k ∉ N j := fun hk' => Finset.disjoint_left.mp hUN hk hk'
      exact Finset.disjoint_left.mp (hN j k hjk hkN) hi hik
    dsimp only [w]
    simp only [uniform_avoidProbability]
    rw [uniform_avoid_difference, uniform_avoid_singleton]
    exact uniformProbability_independent_of_disjoint_coordinates β _ _ hdis _ _
      (hA j) (dependsOn_avoidance A S hA U)
  obtain ⟨hx, hcond⟩ := local_lemma_weight_condition p N hp0 hsmall hsum
  have hlll : ∀ j, 1 - avoidProbability w A {j} ≤
      (2 * p j) * ∏ k ∈ N j, (1 - 2 * p k) := by
    intro j
    dsimp only [w]
    rw [uniform_avoidProbability, uniform_avoid_singleton]
    exact (hp j).trans (hcond j)
  have hpos := finite_asymmetric_local_lemma w A N (fun j => 2 * p j) hw0 hw1 hind
    (fun j => (hx j).1) (fun j => (hx j).2) hlll Finset.univ
  obtain ⟨ω, hω⟩ := exists_avoiding_outcome_of_positive w A Finset.univ hpos
  exact ⟨ω, fun j => hω j (Finset.mem_univ _)⟩

end DirectedCycles
