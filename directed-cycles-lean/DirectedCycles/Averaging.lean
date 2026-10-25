module

public import DirectedCycles.WeightedCuts
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Uniform averaging over a finite group, written as a finite real sum. -/
noncomputable def averageWeight (G : Type*) {V : Type*} [Group G] [Fintype G]
    [MulAction G V] (w : V → V → ℝ) (x y : V) : ℝ :=
  (∑ g : G, w (g • x) (g • y)) / Fintype.card G

theorem averageWeight_nonneg (G : Type*) {V : Type*} [Group G] [Fintype G]
    [MulAction G V] (w : V → V → ℝ) (hn : ∀ x y, 0 ≤ w x y) :
    ∀ x y, 0 ≤ averageWeight G w x y := by
  intro x y
  apply div_nonneg
  · exact Finset.sum_nonneg (fun g _ => hn _ _)
  · positivity

/-- Right translation permutes the averaging group, so the averaged weight
is invariant under the given action. -/
theorem averageWeight_invariant (G : Type*) {V : Type*} [Group G] [Fintype G]
    [MulAction G V] (w : V → V → ℝ) (a : G) (x y : V) :
    averageWeight G w (a • x) (a • y) = averageWeight G w x y := by
  unfold averageWeight
  congr 1
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight a) (fun g => w (g • x) (g • y))

theorem averageWeight_support (G : Type*) {V : Type*} [Group G] [Fintype G]
    [MulAction G V] (D : Digraph V) (w : V → V → ℝ)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (hw : ∀ x y, ¬D x y → w x y = 0) :
    ∀ x y, ¬D x y → averageWeight G w x y = 0 := by
  intro x y hxy
  unfold averageWeight
  have he : ∑ g : G, w (g • x) (g • y) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    exact hw _ _ (fun h => hxy ((hD g x y).mp h))
  rw [he, zero_div]

/-- Averaging permutations of a finite vertex set preserves total weight. -/
theorem averageWeight_total (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (w : V → V → ℝ) :
    ∑ x, ∑ y, averageWeight G w x y = ∑ x, ∑ y, w x y := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ x : V, ∑ y : V, ∑ g : G, w (g • x) (g • y)) =
      ∑ g : G, ∑ x : V, ∑ y : V, w (g • x) (g • y) := by
    calc _ = ∑ x : V, ∑ g : G, ∑ y : V, w (g • x) (g • y) :=
           Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
         _ = _ := Finset.sum_comm
  have hg : ∀ g : G, (∑ x : V, ∑ y : V, w (g • x) (g • y)) = ∑ x, ∑ y, w x y := by
    intro g
    have hi : ∀ x, (∑ y : V, w (g • x) (g • y)) = ∑ y, w (g • x) y := by
      intro x
      exact Equiv.sum_comp (MulAction.toPerm g) (fun y => w (g • x) y)
    simp_rw [hi]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun x => ∑ y, w x y)
  simp only [averageWeight, ← Finset.sum_div, he, hg, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hc

/-- Transitive averaging produces a balanced directed weight. -/
theorem averageWeight_balanced (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (w : V → V → ℝ)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) :
    ∀ x, outWeight (averageWeight G w) x = inWeight (averageWeight G w) x := by
  apply invariant_weights_balanced
  intro x y
  obtain ⟨g, hg⟩ := ht x y
  exact ⟨MulAction.toPerm g, hg, fun u v => averageWeight_invariant G w g u v⟩

/-- A permutation carries the complement of a finite set to the complement
of its image. -/
theorem equiv_map_compl {V : Type*} [Fintype V] [DecidableEq V]
    (g : V ≃ V) (S : Finset V) :
    (S.map g.toEmbedding)ᶜ = Sᶜ.map g.toEmbedding := by
  ext x
  simp

/-- Pulling back a weight by a permutation is the same as applying that
permutation to the cut. -/
theorem cutOut_equiv {V : Type*} [Fintype V] [DecidableEq V]
    (g : V ≃ V) (w : V → V → ℝ) (S : Finset V) :
    cutOut (fun x y => w (g x) (g y)) S = cutOut w (S.map g.toEmbedding) := by
  simp only [cutOut, equiv_map_compl, Finset.sum_map, Equiv.toEmbedding_apply]

theorem cutIn_equiv {V : Type*} [Fintype V] [DecidableEq V]
    (g : V ≃ V) (w : V → V → ℝ) (S : Finset V) :
    cutIn (fun x y => w (g x) (g y)) S = cutIn w (S.map g.toEmbedding) := by
  simp only [cutIn, equiv_map_compl, Finset.sum_map, Equiv.toEmbedding_apply]

theorem averageWeight_cutOut (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V] (w : V → V → ℝ) (S : Finset V) :
    cutOut (averageWeight G w) S =
      (∑ g : G, cutOut w (S.map (MulAction.toPerm g).toEmbedding)) / Fintype.card G := by
  unfold cutOut averageWeight
  simp only [← Finset.sum_div]
  congr 1
  calc _ = ∑ x ∈ S, ∑ g : G, ∑ y ∈ Sᶜ, w (g • x) (g • y) :=
         Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
       _ = ∑ g : G, ∑ x ∈ S, ∑ y ∈ Sᶜ, w (g • x) (g • y) := Finset.sum_comm
       _ = _ := Finset.sum_congr rfl (fun g _ => cutOut_equiv (MulAction.toPerm g) w S)

theorem averageWeight_cutIn (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V] (w : V → V → ℝ) (S : Finset V) :
    cutIn (averageWeight G w) S =
      (∑ g : G, cutIn w (S.map (MulAction.toPerm g).toEmbedding)) / Fintype.card G := by
  unfold cutIn averageWeight
  simp only [← Finset.sum_div]
  congr 1
  calc _ = ∑ x ∈ Sᶜ, ∑ g : G, ∑ y ∈ S, w (g • x) (g • y) :=
         Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
       _ = ∑ g : G, ∑ x ∈ Sᶜ, ∑ y ∈ S, w (g • x) (g • y) := Finset.sum_comm
       _ = _ := Finset.sum_congr rfl (fun g _ => cutIn_equiv (MulAction.toPerm g) w S)

/-- Uniform lower bounds for all translated cuts survive averaging. -/
theorem averageWeight_cut_lower (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [DecidableEq V] [MulAction G V] (w : V → V → ℝ)
    (S : Finset V) (L : ℝ)
    (hL : ∀ g : G, L ≤ cutOut w (S.map (MulAction.toPerm g).toEmbedding) +
      cutIn w (S.map (MulAction.toPerm g).toEmbedding)) :
    L ≤ cutOut (averageWeight G w) S + cutIn (averageWeight G w) S := by
  rw [averageWeight_cutOut, averageWeight_cutIn, ← add_div, ← Finset.sum_add_distrib]
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
  calc L * Fintype.card G = ∑ _g : G, L := by simp [mul_comm]
       _ ≤ _ := Finset.sum_le_sum (fun g _ => hL g)

/-- Transitivity spreads the total averaged weight evenly over the vertices,
so a bound on total weight gives the needed incoming and outgoing capacities. -/
theorem averageWeight_capacity (G : Type*) {V : Type*} [Group G] [Fintype G]
    [Fintype V] [MulAction G V] (w : V → V → ℝ) (a : ℝ)
    (ht : ∀ x y : V, ∃ g : G, g • x = y)
    (hmass : ∑ x, ∑ y, w x y ≤ (Fintype.card V : ℝ) * a) :
    ∀ x, inWeight (averageWeight G w) x ≤ a ∧ outWeight (averageWeight G w) x ≤ a := by
  intro x
  let : Nonempty V := ⟨x⟩
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hu : ∀ y, outWeight (averageWeight G w) y = outWeight (averageWeight G w) x := by
    intro y
    obtain ⟨g, rfl⟩ := ht x y
    unfold outWeight
    rw [← Equiv.sum_comp (MulAction.toPerm g)]
    exact Finset.sum_congr rfl (fun z _ => averageWeight_invariant G w g x z)
  have hsum : (Fintype.card V : ℝ) * outWeight (averageWeight G w) x =
      ∑ y, ∑ z, w y z := by
    calc _ = ∑ y, outWeight (averageWeight G w) y := by simp [hu]
         _ = ∑ y, ∑ z, w y z := averageWeight_total G w
  have hout : outWeight (averageWeight G w) x ≤ a := by
    apply (mul_le_mul_iff_right₀ hcard).mp
    rw [hsum]
    exact hmass
  exact ⟨by rw [← averageWeight_balanced G w ht x]; exact hout, hout⟩

end DirectedCycles
