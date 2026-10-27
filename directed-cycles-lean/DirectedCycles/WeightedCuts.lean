module

public import DirectedCycles.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

noncomputable def outWeight {V : Type*} [Fintype V] (w : V → V → ℝ) (x : V) : ℝ :=
  ∑ y, w x y

noncomputable def inWeight {V : Type*} [Fintype V] (w : V → V → ℝ) (x : V) : ℝ :=
  ∑ y, w y x

noncomputable def cutOut {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (S : Finset V) : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, w x y

noncomputable def cutIn {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (S : Finset V) : ℝ := ∑ x ∈ Sᶜ, ∑ y ∈ S, w x y

/-- Cancelling the internal contributions shows that a balanced weight has
identical entering and leaving weight across every cut. -/
theorem weighted_cut_balance {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (hb : ∀ x, outWeight w x = inWeight w x) (S : Finset V) :
    cutOut w S = cutIn w S := by
  have he : ∑ x ∈ S, outWeight w x = ∑ x ∈ S, inWeight w x := by
    exact Finset.sum_congr rfl (fun x _ => hb x)
  have ho : ∑ x ∈ S, outWeight w x =
      (∑ x ∈ S, ∑ y ∈ S, w x y) + cutOut w S := by
    simp only [outWeight, cutOut, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact (Finset.sum_add_sum_compl S (fun y => w x y)).symm
  have hi : ∑ x ∈ S, inWeight w x =
      (∑ x ∈ S, ∑ y ∈ S, w x y) + cutIn w S := by
    calc (∑ x ∈ S, inWeight w x)
        = (∑ x ∈ S, ∑ y ∈ S, w y x) + (∑ x ∈ S, ∑ y ∈ Sᶜ, w y x) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          exact (Finset.sum_add_sum_compl S (fun y => w y x)).symm
      _ = (∑ x ∈ S, ∑ y ∈ S, w x y) + cutIn w S :=
        congrArg₂ (· + ·) Finset.sum_comm Finset.sum_comm
  rw [ho, hi] at he
  exact add_left_cancel he

/-- Equal constant row and column sums have the same value on a nonempty
finite vertex set. -/
theorem constant_weights_balanced {V : Type*} [Fintype V] [Nonempty V]
    (w : V → V → ℝ) (a b : ℝ)
    (ho : ∀ x, outWeight w x = a) (hi : ∀ x, inWeight w x = b) : a = b := by
  have he : (Fintype.card V : ℝ) * a = (Fintype.card V : ℝ) * b := by
    calc (Fintype.card V : ℝ) * a = ∑ x, outWeight w x := by simp [ho]
         _ = ∑ x, inWeight w x := Finset.sum_comm
         _ = (Fintype.card V : ℝ) * b := by simp [hi]
  exact mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero) he

/-- Invariance and transitivity make both incoming and outgoing weights
constant; finite double counting then gives balance at every vertex. -/
theorem invariant_weights_balanced {V : Type*} [Fintype V]
    (w : V → V → ℝ)
    (ht : ∀ x y, ∃ g : V ≃ V, g x = y ∧ ∀ u v, w (g u) (g v) = w u v) :
    ∀ x, outWeight w x = inWeight w x := by
  intro x
  let : Nonempty V := ⟨x⟩
  have ho : ∀ y, outWeight w y = outWeight w x := by
    intro y
    obtain ⟨g, rfl, hw⟩ := ht x y
    change ∑ v, w (g x) v = ∑ v, w x v
    rw [← Equiv.sum_comp g]
    exact Finset.sum_congr rfl (fun v _ => hw x v)
  have hi : ∀ y, inWeight w y = inWeight w x := by
    intro y
    obtain ⟨g, rfl, hw⟩ := ht x y
    change ∑ v, w v (g x) = ∑ v, w v x
    rw [← Equiv.sum_comp g]
    exact Finset.sum_congr rfl (fun v _ => hw v x)
  exact constant_weights_balanced w _ _ ho hi

noncomputable def outBoundary {V : Type*} [Fintype V] (D : Digraph V)
    (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => y ∉ S ∧ ∃ x ∈ S, D x y)

noncomputable def inBoundary {V : Type*} [Fintype V] (D : Digraph V)
    (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => x ∉ S ∧ ∃ y ∈ S, D x y)

@[simp] theorem mem_outBoundary {V : Type*} [Fintype V] (D : Digraph V)
    (S : Finset V) (y : V) : y ∈ outBoundary D S ↔ y ∉ S ∧ ∃ x ∈ S, D x y := by
  classical
  simp [outBoundary]

@[simp] theorem mem_inBoundary {V : Type*} [Fintype V] (D : Digraph V)
    (S : Finset V) (x : V) : x ∈ inBoundary D S ↔ x ∉ S ∧ ∃ y ∈ S, D x y := by
  classical
  simp [inBoundary]

/-- A per-vertex incoming capacity bounds the total outgoing cut weight by
the capacity times the number of external out-neighbors. -/
theorem cutOut_le_boundary_capacity {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (w : V → V → ℝ) (S : Finset V) (a : ℝ)
    (hn : ∀ x y, 0 ≤ w x y) (hs : ∀ x y, ¬ D x y → w x y = 0)
    (hi : ∀ y, inWeight w y ≤ a) :
    cutOut w S ≤ (outBoundary D S).card * a := by
  classical
  have hout : outBoundary D S ⊆ Sᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr ((mem_outBoundary D S v).mp hv).1
  have he : cutOut w S = ∑ y ∈ outBoundary D S, ∑ x ∈ S, w x y := by
    rw [cutOut, Finset.sum_comm]
    symm
    apply Finset.sum_subset hout
    intro y hy hyb
    apply Finset.sum_eq_zero
    intro x hx
    apply hs x y
    intro hxy
    apply hyb
    exact (mem_outBoundary D S y).mpr ⟨Finset.mem_compl.mp hy, x, hx, hxy⟩
  rw [he]
  calc (∑ y ∈ outBoundary D S, ∑ x ∈ S, w x y)
      ≤ ∑ y ∈ outBoundary D S, a := by
        apply Finset.sum_le_sum
        intro y _
        apply le_trans _ (hi y)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun x _ _ => hn x y)
    _ = (outBoundary D S).card * a := by simp

/-- The corresponding bound on the external in-boundary. -/
theorem cutIn_le_boundary_capacity {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (w : V → V → ℝ) (S : Finset V) (a : ℝ)
    (hn : ∀ x y, 0 ≤ w x y) (hs : ∀ x y, ¬ D x y → w x y = 0)
    (ho : ∀ x, outWeight w x ≤ a) :
    cutIn w S ≤ (inBoundary D S).card * a := by
  have h := cutOut_le_boundary_capacity (fun x y => D y x) (fun x y => w y x)
    S a (fun x y => hn y x) (fun x y => hs y x) ho
  have he : cutOut (fun x y => w y x) S = cutIn w S := Finset.sum_comm
  rw [he] at h
  exact h

/-- The finite weighted-cut implication used in Lemma 4.1. The routing
construction must separately supply the cut lower bound and capacities. -/
theorem boundary_lower_bound_of_weights {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (w : V → V → ℝ) (S : Finset V) (a L : ℝ) (ha : 0 < a)
    (hn : ∀ x y, 0 ≤ w x y) (hs : ∀ x y, ¬ D x y → w x y = 0)
    (hb : ∀ x, outWeight w x = inWeight w x)
    (hi : ∀ x, inWeight w x ≤ a) (ho : ∀ x, outWeight w x ≤ a)
    (hl : 2 * L ≤ cutOut w S + cutIn w S) :
    L / a ≤ (outBoundary D S).card ∧ L / a ≤ (inBoundary D S).card := by
  have he := weighted_cut_balance w hb S
  have hout := cutOut_le_boundary_capacity D w S a hn hs hi
  have hin := cutIn_le_boundary_capacity D w S a hn hs ho
  constructor
  · apply (div_le_iff₀ ha).mpr
    linarith
  · apply (div_le_iff₀ ha).mpr
    linarith

end DirectedCycles
