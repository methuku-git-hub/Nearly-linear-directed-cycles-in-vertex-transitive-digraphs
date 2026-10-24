import DirectedCycles.WeightedCuts
import DirectedCycles.Paths

set_option autoImplicit false
namespace DirectedCycles

/-- The traversal count of an ordered edge in a finite walk. It counts
multiplicity, so the routing estimates do not assume distinct routes. -/
noncomputable def walkLoad {V : Type*} [DecidableEq V] (l : List V) (x y : V) : ℝ :=
  match l with
  | a :: b :: t => (if x = a ∧ y = b then 1 else 0) + walkLoad (b :: t) x y
  | _ => 0

theorem walkLoad_nonneg {V : Type*} [DecidableEq V] (l : List V) (x y : V) :
    0 ≤ walkLoad l x y := by
  induction l using List.twoStepInduction with
  | nil => simp [walkLoad]
  | singleton a => simp [walkLoad]
  | cons_cons a b t _ ih =>
    simp only [walkLoad]
    exact add_nonneg (by split_ifs <;> norm_num) (ih b)

theorem walkLoad_support {V : Type*} [DecidableEq V] {D : Digraph V}
    (l : List V) (hc : l.IsChain D) (x y : V) (hn : ¬D x y) :
    walkLoad l x y = 0 := by
  induction l using List.twoStepInduction with
  | nil => simp [walkLoad]
  | singleton a => simp [walkLoad]
  | cons_cons a b t _ ih =>
    have hh : ¬(x = a ∧ y = b) := by
      rintro ⟨rfl, rfl⟩
      exact hn hc.rel
    simp only [walkLoad, ite_eq_right hh, zero_add]
    exact ih b hc.tail

theorem walkLoad_total {V : Type*} [Fintype V] [DecidableEq V] (l : List V) :
    ∑ x, ∑ y, walkLoad l x y = (l.length - 1 : ℕ) := by
  induction l using List.twoStepInduction with
  | nil => simp [walkLoad]
  | singleton a => simp [walkLoad]
  | cons_cons a b t _ ih =>
    simp only [walkLoad, Finset.sum_add_distrib]
    rw [ih]
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have he : (∑ x : V, ∑ y : V, if x = a ∧ y = b then (1 : ℝ) else 0) = 1 := by
      simp [ite_and]
    rw [he]
    ring

/-- Adding one traversed edge changes the total cut crossing weight by one
exactly when its two endpoints are on opposite sides. -/
theorem walkLoad_cut_cons {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (a b : V) (t : List V) :
    cutOut (walkLoad (a :: b :: t)) S + cutIn (walkLoad (a :: b :: t)) S =
      (if (a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S) then 1 else 0) +
      (cutOut (walkLoad (b :: t)) S + cutIn (walkLoad (b :: t)) S) := by
  simp only [cutOut, cutIn, walkLoad, Finset.sum_add_distrib]
  have ho : (∑ x ∈ S, ∑ y ∈ Sᶜ, if x = a ∧ y = b then (1 : ℝ) else 0) =
      if a ∈ S ∧ b ∉ S then 1 else 0 := by
    simp [ite_and]
  have hi : (∑ x ∈ Sᶜ, ∑ y ∈ S, if x = a ∧ y = b then (1 : ℝ) else 0) =
      if a ∉ S ∧ b ∈ S then 1 else 0 := by
    simp [ite_and]
  rw [ho, hi]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb] <;> ring

theorem walkLoad_cut_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (l : List V) :
    0 ≤ cutOut (walkLoad l) S + cutIn (walkLoad l) S := by
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro x hx <;>
    apply Finset.sum_nonneg <;> intro y hy <;> exact walkLoad_nonneg l x y

/-- Every walk between opposite sides of a cut contributes at least one
crossing, irrespective of the orientations available in the digraph. -/
theorem walkLoad_cut_crossing {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (l : List V) :
    ∀ x ∈ l.head?, ∀ y ∈ l.getLast?,
      ((x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S)) →
      1 ≤ cutOut (walkLoad l) S + cutIn (walkLoad l) S := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    intro x hx y hy hxy
    have hx' : x = a := by simpa [eq_comm] using hx
    have hy' : y = a := by simpa [eq_comm] using hy
    subst x; subst y
    simp at hxy
  | cons_cons a b t _ ih =>
    intro x hx y hy hxy
    have hx' : x = a := by simpa [eq_comm] using hx
    subst x
    have hy' : y ∈ (b :: t).getLast? := by simpa using hy
    rw [walkLoad_cut_cons]
    by_cases hab : (a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S)
    · rw [ite_eq_left hab]
      have := walkLoad_cut_nonneg S (b :: t)
      linarith
    · rw [ite_eq_right hab, zero_add]
      apply ih b b (by simp) y hy'
      tauto

/-- Assign each traversal's undirected edge weight to its available directed
orientation, dividing evenly when both orientations occur. -/
noncomputable def orientWeight {V : Type*} (D : Digraph V) (w : V → V → ℝ)
    (x y : V) : ℝ := by
  classical
  exact if D x y then if D y x then (w x y + w y x) / 2 else w x y + w y x else 0

theorem orientWeight_nonneg {V : Type*} (D : Digraph V) (w : V → V → ℝ)
    (hn : ∀ x y, 0 ≤ w x y) : ∀ x y, 0 ≤ orientWeight D w x y := by
  classical
  intro x y
  unfold orientWeight
  split_ifs
  · exact div_nonneg (add_nonneg (hn x y) (hn y x)) (by norm_num)
  · exact add_nonneg (hn x y) (hn y x)
  · exact le_rfl

theorem orientWeight_support {V : Type*} (D : Digraph V) (w : V → V → ℝ)
    (x y : V) (hn : ¬D x y) : orientWeight D w x y = 0 := by
  classical
  simp [orientWeight, hn]

/-- Reorienting preserves the total weight of each unordered pair. -/
theorem orientWeight_pair {V : Type*} (D : Digraph V) (w : V → V → ℝ)
    (hs : ∀ x y, ¬(D x y ∨ D y x) → w x y = 0) (x y : V) :
    orientWeight D w x y + orientWeight D w y x = w x y + w y x := by
  classical
  unfold orientWeight
  by_cases hxy : D x y <;> by_cases hyx : D y x
  · simp only [ite_eq_left hxy, ite_eq_left hyx]; ring
  · simp only [ite_eq_left hxy, ite_eq_right hyx, add_zero]
  · simp only [ite_eq_right hxy, ite_eq_left hyx, zero_add]; ring
  · rw [hs x y (by tauto), hs y x (by tauto)]
    simp [hxy, hyx]

theorem orientWeight_total {V : Type*} [Fintype V]
    (D : Digraph V) (w : V → V → ℝ)
    (hs : ∀ x y, ¬(D x y ∨ D y x) → w x y = 0) :
    ∑ x, ∑ y, orientWeight D w x y = ∑ x, ∑ y, w x y := by
  have he : (∑ x, ∑ y, orientWeight D w x y) + (∑ x, ∑ y, orientWeight D w x y) =
      (∑ x, ∑ y, w x y) + (∑ x, ∑ y, w x y) := by
    calc _ = ∑ x, ∑ y, (orientWeight D w x y + orientWeight D w y x) := by
           simp only [Finset.sum_add_distrib]
           exact congrArg₂ (· + ·) rfl Finset.sum_comm
         _ = ∑ x, ∑ y, (w x y + w y x) := by
           apply Finset.sum_congr rfl
           intro x _
           exact Finset.sum_congr rfl (fun y _ => orientWeight_pair D w hs x y)
         _ = _ := by
           simp only [Finset.sum_add_distrib]
           exact congrArg₂ (· + ·) rfl Finset.sum_comm
  linarith

theorem orientWeight_cut {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (w : V → V → ℝ) (S : Finset V)
    (hs : ∀ x y, ¬(D x y ∨ D y x) → w x y = 0) :
    cutOut (orientWeight D w) S + cutIn (orientWeight D w) S =
      cutOut w S + cutIn w S := by
  have pairSum : ∀ f : V → V → ℝ, cutOut f S + cutIn f S =
      ∑ x ∈ S, ∑ y ∈ Sᶜ, (f x y + f y x) := by
    intro f
    simp only [cutOut, cutIn, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) rfl Finset.sum_comm
  rw [pairSum, pairSum]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_congr rfl (fun y _ => orientWeight_pair D w hs x y)

end DirectedCycles
