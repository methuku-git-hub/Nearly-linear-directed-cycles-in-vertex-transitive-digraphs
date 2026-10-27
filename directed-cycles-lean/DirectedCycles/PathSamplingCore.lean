module

public import DirectedCycles.CollisionLoads
public import DirectedCycles.PathSupports
public import DirectedCycles.Shortening

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

set_option maxHeartbeats 1000000 in
/-- The path-level local-lemma argument. Sampling distributions, path lengths,
and the global load are explicit hypotheses here; the separate equivariant
experiment must construct and prove those facts before applying this lemma. -/
theorem cyclic_path_sampling {V : Type*} [Fintype V] (D : Digraph V)
    (n : ℕ) (hn : 4 ≤ n) (β : Fin n → Type*)
    [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (P : Fin n → (∀ i, β i) → List V)
    (hP : ∀ i, DependsOn (stepSupport (finRotate n) i) (P i))
    (hloop : ∀ ω, IsPathLoop D (fun i => P i ω))
    (L T : ℝ) (hL : 0 ≤ L)
    (hlen : ∀ i ω, ((P i ω).length : ℝ) ≤ T)
    (hload : ∀ v, (∑ i, uniformProbability (fun ω => v ∈ P i ω)) ≤ L)
    (hLT : L * T ≤ 1 / 48) :
    ∃ C : Cycle D, n ≤ C.length := by
  let a : Fin n → V → ℝ := fun i v => uniformProbability (fun ω => v ∈ P i ω)
  let w : Fin n → Fin n → ℝ := fun i j => ∑ v, a i v * a j v
  have ha0 : ∀ i v, 0 ≤ a i v := fun i v => uniformProbability_nonneg _
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j =>
    Finset.sum_nonneg (fun v _ => mul_nonneg (ha0 i v) (ha0 j v))
  have hmass : ∀ i, (∑ v, a i v) ≤ T := fun i => path_vertex_load_sum (P i) T (hlen i)
  have hrow : ∀ i, (∑ j, w i j) ≤ 1 / 48 := fun i =>
    (collision_weight_row_bound a ha0 L T hL hload hmass i).trans hLT
  have hsym : ∀ i j, w i j = w j i := by
    intro i j
    apply Finset.sum_congr rfl
    intro v _
    exact mul_comm _ _
  have hcol : ∀ j, (∑ i, w i j) ≤ 1 / 48 := by
    intro j
    simpa only [hsym] using hrow j
  let A : CollisionPair (finRotate n) → (∀ i, β i) → Prop :=
    fun p ω => ∃ v, v ∈ P p.val.1 ω ∧ v ∈ P p.val.2 ω
  let pweight : CollisionPair (finRotate n) → ℝ := fun p => w p.val.1 p.val.2
  have hp : ∀ p, uniformProbability (A p) ≤ pweight p := by
    intro p
    exact collision_probability_bound β (stepSupport (finRotate n) p.val.1)
      (stepSupport (finRotate n) p.val.2) p.property (P p.val.1) (P p.val.2)
      (hP p.val.1) (hP p.val.2)
  have hsmall : ∀ p, pweight p ≤ 1 / 48 := by
    intro p
    exact (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      hw0 p.val.1 j) (Finset.mem_univ p.val.2)).trans (hrow p.val.1)
  have hsum : ∀ p, (∑ q ∈ collisionNeighbors (finRotate n) p, pweight q) ≤ 1 / 4 :=
    collisionNeighbors_weight_bound (finRotate n) w hw0 hrow hcol
  obtain ⟨ω, hω⟩ := finite_coordinate_local_lemma β A (collisionSupport (finRotate n))
    (collisionNeighbors (finRotate n)) (collision_dependsOn (finRotate n) P hP)
    (fun p q _ hq => collisionSupport_disjoint_of_not_neighbor (finRotate n) p q hq)
    pweight hp (fun p => hw0 p.val.1 p.val.2) hsmall hsum
  apply shortening_path_loop hn (fun i => P i ω) (hloop ω)
  intro i j hij hji hij'
  let p : CollisionPair (finRotate n) :=
    ⟨(i, j), (stepSupport_disjoint_iff (finRotate n) i j).mpr ⟨hij, hji, hij'⟩⟩
  intro v hvi hvj
  exact hω p ⟨v, hvi, hvj⟩

end DirectedCycles
