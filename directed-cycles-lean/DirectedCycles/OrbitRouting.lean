module

public import DirectedCycles.RoutingWeights
public import DirectedCycles.Averaging

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Ordered distinct pairs to be routed. -/
abbrev RoutedPair {V : Type*} (E : V → V → Prop) :=
  {p : V × V // E p.1 p.2 ∧ p.1 ≠ p.2}

theorem sum_routedPair {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (f : V × V → ℝ) :
    ∑ p : RoutedPair E, f p.val =
      ∑ x : V, ∑ y : V, if E x y ∧ x ≠ y then f (x, y) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : V × V => E p.1 p.2 ∧ p.1 ≠ p.2))
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]

noncomputable def crossWeight {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (S : Finset V) : ℝ :=
  cutOut (fun x y => if E x y then 1 else 0) S

theorem sum_compl_indicator {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (f : V → ℝ) :
    ∑ x ∈ Sᶜ, f x = ∑ x, if x ∈ S then 0 else f x := by
  have hf : Finset.univ.filter (fun x => x ∉ S) = Sᶜ := by ext x; simp
  calc (∑ x ∈ Sᶜ, f x) = ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), f x := by rw [hf]
       _ = ∑ x, if x ∉ S then f x else 0 := Finset.sum_filter _ _
       _ = _ := by simp only [ite_not]

theorem cutOut_indicator {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (S : Finset V) :
    cutOut w S = ∑ x : V, ∑ y : V, if x ∈ S ∧ y ∉ S then w x y else 0 := by
  simp [cutOut, ite_and, Finset.sum_ite_irrel]
  apply Finset.sum_congr rfl
  intro x _
  exact sum_compl_indicator S (w x)

theorem cutIn_indicator {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → V → ℝ) (S : Finset V) :
    cutIn w S = ∑ x : V, ∑ y : V, if x ∉ S ∧ y ∈ S then w x y else 0 := by
  simp [cutIn, ite_and, Finset.sum_ite_irrel]
  exact sum_compl_indicator S (fun x => ∑ y ∈ S, w x y)

theorem crossWeight_invariant {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (g : V ≃ V)
    (hg : ∀ x y, E (g x) (g y) ↔ E x y) (S : Finset V) :
    crossWeight E (S.map g.toEmbedding) = crossWeight E S := by
  classical
  unfold crossWeight
  rw [← cutOut_equiv]
  simp only [hg]

theorem routed_cross_count {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (he : ∀ {x y}, E x y → E y x) (S : Finset V) :
    (∑ p : RoutedPair E,
      if (p.val.1 ∈ S ∧ p.val.2 ∉ S) ∨ (p.val.1 ∉ S ∧ p.val.2 ∈ S)
      then (1 : ℝ) else 0) = 2 * crossWeight E S := by
  rw [sum_routedPair E (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then 1 else 0)]
  have hp : ∀ x y : V,
      (if E x y ∧ x ≠ y then
        if (x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S) then (1 : ℝ) else 0 else 0) =
      (if x ∈ S ∧ y ∉ S then if E x y then 1 else 0 else 0) +
      (if x ∉ S ∧ y ∈ S then if E x y then 1 else 0 else 0) := by
    intro x y
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp [hx, hy]
    · have hxy : x ≠ y := by intro h; subst y; contradiction
      simp [hx, hy, hxy]
    · have hxy : x ≠ y := by intro h; subst y; contradiction
      simp [hx, hy, hxy]
    · simp [hx, hy]
  simp_rw [hp]
  simp_rw [Finset.sum_add_distrib]
  rw [← cutOut_indicator, ← cutIn_indicator]
  have hin : cutIn (fun x y => if E x y then (1 : ℝ) else 0) S = crossWeight E S := by
    unfold cutIn crossWeight cutOut
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [show E y x ↔ E x y from ⟨he, he⟩]
  rw [hin]
  change crossWeight E S + crossWeight E S = 2 * crossWeight E S
  ring

/-- The total traversal load of a finite indexed family of routes. -/
noncomputable def familyLoad {I V : Type*} [Fintype I] [DecidableEq V]
    (P : I → List V) (x y : V) : ℝ := ∑ i, walkLoad (P i) x y

theorem familyLoad_nonneg {I V : Type*} [Fintype I] [DecidableEq V]
    (P : I → List V) : ∀ x y, 0 ≤ familyLoad P x y := by
  intro x y
  exact Finset.sum_nonneg (fun i _ => walkLoad_nonneg (P i) x y)

theorem familyLoad_support {I V : Type*} [Fintype I] [DecidableEq V]
    {D : Digraph V} (P : I → List V) (hc : ∀ i, (P i).IsChain D) :
    ∀ x y, ¬D x y → familyLoad P x y = 0 := by
  intro x y hn
  exact Finset.sum_eq_zero (fun i _ => walkLoad_support (P i) (hc i) x y hn)

theorem familyLoad_total {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (P : I → List V) : ∑ x, ∑ y, familyLoad P x y = ∑ i, (((P i).length - 1 : ℕ) : ℝ) := by
  unfold familyLoad
  calc _ = ∑ x : V, ∑ i : I, ∑ y : V, walkLoad (P i) x y :=
         Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
       _ = ∑ i : I, ∑ x : V, ∑ y : V, walkLoad (P i) x y := Finset.sum_comm
       _ = _ := Finset.sum_congr rfl (fun i _ => walkLoad_total (P i))

theorem familyLoad_cut {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (P : I → List V) (S : Finset V) :
    cutOut (familyLoad P) S + cutIn (familyLoad P) S =
      ∑ i, (cutOut (walkLoad (P i)) S + cutIn (walkLoad (P i)) S) := by
  have out : cutOut (familyLoad P) S = ∑ i, cutOut (walkLoad (P i)) S := by
    unfold cutOut familyLoad
    calc _ = ∑ x ∈ S, ∑ i : I, ∑ y ∈ Sᶜ, walkLoad (P i) x y :=
           Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
         _ = _ := Finset.sum_comm
  have inn : cutIn (familyLoad P) S = ∑ i, cutIn (walkLoad (P i)) S := by
    unfold cutIn familyLoad
    calc _ = ∑ x ∈ Sᶜ, ∑ i : I, ∑ y ∈ S, walkLoad (P i) x y :=
           Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
         _ = _ := Finset.sum_comm
  rw [out, inn, Finset.sum_add_distrib]

/-- Routing every ordered pair in a symmetric relation forces twice the
one-direction crossing-pair count to cross any cut. -/
theorem familyLoad_routed_cut {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (he : ∀ {x y}, E x y → E y x)
    (P : RoutedPair E → List V)
    (hh : ∀ p, (P p).head? = some p.val.1)
    (ht : ∀ p, (P p).getLast? = some p.val.2) (S : Finset V) :
    2 * crossWeight E S ≤ cutOut (familyLoad P) S + cutIn (familyLoad P) S := by
  rw [familyLoad_cut, ← routed_cross_count E he S]
  apply Finset.sum_le_sum
  intro p _
  split_ifs with hp
  · exact walkLoad_cut_crossing S (P p) p.val.1 (hh p) p.val.2 (ht p) hp
  · exact walkLoad_cut_nonneg S (P p)

end DirectedCycles
