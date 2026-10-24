import DirectedCycles.UniformFinite

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The finite union bound, in the same uniform probability space as the
coordinate local lemma. -/
theorem uniformProbability_exists_le_sum {Ω V : Type*} [Fintype Ω] [Fintype V]
    (A : V → Ω → Prop) :
    uniformProbability (fun ω => ∃ v, A v ω) ≤ ∑ v, uniformProbability (A v) := by
  unfold uniformProbability
  rw [← uniformAverage_sum]
  apply uniformAverage_mono
  intro ω
  by_cases h : ∃ v, A v ω
  · obtain ⟨v, hv⟩ := h
    have hs := Finset.single_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) =>
      eventIndicator_nonneg (A u ω)) (Finset.mem_univ v)
    calc eventIndicator (∃ v, A v ω) = eventIndicator (A v ω) := by
           simp [eventIndicator, hv, show ∃ v, A v ω from ⟨v, hv⟩]
         _ ≤ ∑ u, eventIndicator (A u ω) := hs
  · rw [show eventIndicator (∃ v, A v ω) = 0 by simp [eventIndicator, h]]
    exact Finset.sum_nonneg (fun v _ => eventIndicator_nonneg (A v ω))

/-- Collision probability is bounded by the scalar product of vertex loads
when the two path-valued functions use disjoint random coordinates. -/
theorem collision_probability_bound {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I]
    (β : I → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (S T : Finset I) (hST : Disjoint S T) (P Q : (∀ i, β i) → List V)
    (hP : DependsOn S P) (hQ : DependsOn T Q) :
    uniformProbability (fun ω => ∃ v, v ∈ P ω ∧ v ∈ Q ω) ≤
      ∑ v, uniformProbability (fun ω => v ∈ P ω) * uniformProbability (fun ω => v ∈ Q ω) := by
  apply (uniformProbability_exists_le_sum (fun v ω => v ∈ P ω ∧ v ∈ Q ω)).trans_eq
  apply Finset.sum_congr rfl
  intro v _
  apply uniformProbability_independent_of_disjoint_coordinates β S T hST
  · intro ω ω' he
    exact congrArg (fun l => v ∈ l) (hP ω ω' he)
  · intro ω ω' he
    exact congrArg (fun l => v ∈ l) (hQ ω ω' he)

/-- The expected number of vertices in a path bounds the sum of its vertex
inclusion probabilities, without requiring simplicity for this inequality. -/
theorem path_vertex_load_sum {Ω V : Type*} [Fintype Ω] [Nonempty Ω] [Fintype V]
    (P : Ω → List V) (t : ℝ) (ht : ∀ ω, (P ω).length ≤ t) :
    (∑ v, uniformProbability (fun ω => v ∈ P ω)) ≤ t := by
  unfold uniformProbability
  rw [← uniformAverage_sum]
  have hpoint : ∀ ω, (∑ v, eventIndicator (v ∈ P ω)) ≤ t := by
    intro ω
    have he : (∑ v : V, eventIndicator (v ∈ P ω)) = ((P ω).toFinset.card : ℝ) := by
      have hfilter : Finset.univ.filter (fun v => v ∈ P ω) = (P ω).toFinset := by
        ext v; simp
      have hsum : (∑ v : V, eventIndicator (v ∈ P ω)) =
          ∑ v : V, if v ∈ P ω then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ P ω <;> simp [eventIndicator, hv]
      rw [hsum, Finset.sum_boole, hfilter]
    rw [he]
    have hcard : ((P ω).toFinset.card : ℝ) ≤ (P ω).length := by
      exact_mod_cast List.toFinset_card_le (P ω)
    exact hcard.trans (ht ω)
  calc uniformAverage (fun ω => ∑ v, eventIndicator (v ∈ P ω)) ≤
         uniformAverage (fun _ : Ω => t) := uniformAverage_mono hpoint
       _ = t := uniformAverage_const t

/-- The row-sum calculation from the vertex-load estimate. -/
theorem collision_weight_row_bound {I V : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℝ) (h0 : ∀ i v, 0 ≤ a i v)
    (L T : ℝ) (hL : 0 ≤ L)
    (hload : ∀ v, (∑ j, a j v) ≤ L) (hmass : ∀ i, (∑ v, a i v) ≤ T) (i : I) :
    (∑ j, ∑ v, a i v * a j v) ≤ L * T := by
  rw [Finset.sum_comm]
  calc (∑ v, ∑ j, a i v * a j v) ≤ ∑ v, a i v * L := by
         apply Finset.sum_le_sum
         intro v _
         rw [← Finset.mul_sum]
         exact mul_le_mul_of_nonneg_left (hload v) (h0 i v)
       _ = L * ∑ v, a i v := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
       _ ≤ L * T := mul_le_mul_of_nonneg_left (hmass i) hL

end DirectedCycles
