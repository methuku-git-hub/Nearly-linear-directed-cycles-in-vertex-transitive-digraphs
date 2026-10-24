import DirectedCycles.UniformFinite

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

noncomputable def stepSupport {I : Type*} (s : Equiv.Perm I) (i : I) : Finset I := {i, s i}

noncomputable def nearPath {I : Type*} (s : Equiv.Perm I) (i : I) : Finset I :=
  {s.symm i, i, s i}

/-- For a cyclic path indexed by `i`, only its two endpoint coordinates and
its private randomness are used; private randomness is stored at `i`. -/
theorem stepSupport_disjoint_iff {I : Type*} (s : Equiv.Perm I) (i j : I) :
    Disjoint (stepSupport s i) (stepSupport s j) ↔
      i ≠ j ∧ j ≠ s i ∧ i ≠ s j := by
  simp only [stepSupport, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
    Finset.mem_insert, Finset.mem_singleton, not_or, s.injective.ne_iff]
  tauto

theorem stepSupport_disjoint_of_not_near {I : Type*} (s : Equiv.Perm I) (i j : I)
    (h : j ∉ nearPath s i) : Disjoint (stepSupport s i) (stepSupport s j) := by
  have hh : j ≠ s.symm i ∧ j ≠ i ∧ j ≠ s i := by simpa [nearPath] using h
  apply (stepSupport_disjoint_iff s i j).mpr
  refine ⟨Ne.symm hh.2.1, hh.2.2, ?_⟩
  intro he
  apply hh.1
  rw [he, Equiv.symm_apply_apply]

theorem nearPath_card_le {I : Type*} (s : Equiv.Perm I) (i : I) :
    (nearPath s i).card ≤ 3 := by
  dsimp [nearPath]
  calc ({s.symm i, i, s i} : Finset I).card ≤ ({i, s i} : Finset I).card + 1 :=
         Finset.card_insert_le _ _
       _ ≤ 3 := by have h := Finset.card_insert_le i ({s i} : Finset I); simp only [Finset.card_singleton] at h; omega

/-- Ordered pairs are retained in both directions. This doubles the
neighborhood estimate from 1/8 to 1/4, which still suffices for `x = 2p`. -/
abbrev CollisionPair {I : Type*} (s : Equiv.Perm I) :=
  {p : I × I // Disjoint (stepSupport s p.1) (stepSupport s p.2)}

noncomputable def collisionSupport {I : Type*} (s : Equiv.Perm I) (p : CollisionPair s) : Finset I :=
  stepSupport s p.val.1 ∪ stepSupport s p.val.2

noncomputable def nearbyPaths {I : Type*} (s : Equiv.Perm I) (p : CollisionPair s) : Finset I :=
  nearPath s p.val.1 ∪ nearPath s p.val.2

theorem nearbyPaths_card_le {I : Type*} (s : Equiv.Perm I) (p : CollisionPair s) :
    (nearbyPaths s p).card ≤ 6 := by
  have hu := Finset.card_union_le (nearPath s p.val.1) (nearPath s p.val.2)
  have h1 := nearPath_card_le s p.val.1
  have h2 := nearPath_card_le s p.val.2
  dsimp [nearbyPaths]
  omega

noncomputable def collisionNeighbors {I : Type*} [Fintype I] (s : Equiv.Perm I)
    (p : CollisionPair s) : Finset (CollisionPair s) :=
  Finset.univ.filter (fun q => q.val.1 ∈ nearbyPaths s p ∨ q.val.2 ∈ nearbyPaths s p)

/-- The complete dependency-graph condition follows from disjoint random
coordinate supports, including the endpoint shared by adjacent paths. -/
theorem collisionSupport_disjoint_of_not_neighbor {I : Type*} [Fintype I]
    (s : Equiv.Perm I) (p q : CollisionPair s) (h : q ∉ collisionNeighbors s p) :
    Disjoint (collisionSupport s p) (collisionSupport s q) := by
  have hh : q.val.1 ∉ nearbyPaths s p ∧ q.val.2 ∉ nearbyPaths s p := by
    simpa [collisionNeighbors] using h
  have h11 : q.val.1 ∉ nearPath s p.val.1 := fun he => hh.1 (Finset.mem_union.mpr (Or.inl he))
  have h12 : q.val.1 ∉ nearPath s p.val.2 := fun he => hh.1 (Finset.mem_union.mpr (Or.inr he))
  have h21 : q.val.2 ∉ nearPath s p.val.1 := fun he => hh.2 (Finset.mem_union.mpr (Or.inl he))
  have h22 : q.val.2 ∉ nearPath s p.val.2 := fun he => hh.2 (Finset.mem_union.mpr (Or.inr he))
  simp only [collisionSupport, Finset.disjoint_union_left, Finset.disjoint_union_right]
  exact ⟨⟨stepSupport_disjoint_of_not_near s _ _ h11, stepSupport_disjoint_of_not_near s _ _ h12⟩,
    ⟨stepSupport_disjoint_of_not_near s _ _ h21, stepSupport_disjoint_of_not_near s _ _ h22⟩⟩

theorem collision_dependsOn {I V : Type*} {β : I → Type*} (s : Equiv.Perm I)
    (P : I → (∀ i, β i) → List V) (hP : ∀ i, DependsOn (stepSupport s i) (P i))
    (p : CollisionPair s) :
    DependsOn (collisionSupport s p) (fun ω => ∃ v, v ∈ P p.val.1 ω ∧ v ∈ P p.val.2 ω) := by
  intro ω ω' he
  have h1 := hP p.val.1 ω ω' (fun i hi => he i (Finset.mem_union.mpr (Or.inl hi)))
  have h2 := hP p.val.2 ω ω' (fun i hi => he i (Finset.mem_union.mpr (Or.inr hi)))
  simp only [h1, h2]


theorem sum_collisionPair {I : Type*} [Fintype I] (s : Equiv.Perm I) (f : I × I → ℝ) :
    (∑ p : CollisionPair s, f p.val) = ∑ i, ∑ j,
      if Disjoint (stepSupport s i) (stepSupport s j) then f (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : I × I =>
      Disjoint (stepSupport s p.1) (stepSupport s p.2))) (by simp) f,
    Finset.sum_filter, Fintype.sum_prod_type]

/-- At most six path rows and six path columns contribute to the dependency
neighborhood when ordered collision pairs are used. -/
theorem collisionNeighbors_weight_bound {I : Type*} [Fintype I]
    (s : Equiv.Perm I) (w : I → I → ℝ) (h0 : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, (∑ j, w i j) ≤ 1 / 48)
    (hcol : ∀ j, (∑ i, w i j) ≤ 1 / 48) (p : CollisionPair s) :
    (∑ q ∈ collisionNeighbors s p, w q.val.1 q.val.2) ≤ 1 / 4 := by
  let K := nearbyPaths s p
  have hpoint : ∀ i j,
      (if Disjoint (stepSupport s i) (stepSupport s j) then
        if i ∈ K ∨ j ∈ K then w i j else 0 else 0) ≤
      (if i ∈ K then w i j else 0) + (if j ∈ K then w i j else 0) := by
    intro i j
    split_ifs <;> first | tauto | linarith [h0 i j]
  have hsum : (∑ q ∈ collisionNeighbors s p, w q.val.1 q.val.2) ≤
      (∑ i, ∑ j, if i ∈ K then w i j else 0) +
      (∑ i, ∑ j, if j ∈ K then w i j else 0) := by
    dsimp only [collisionNeighbors]
    rw [Finset.sum_filter, sum_collisionPair s (fun q =>
      if q.1 ∈ nearbyPaths s p ∨ q.2 ∈ nearbyPaths s p then w q.1 q.2 else 0)]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hpoint i j))
    simpa only [Finset.sum_add_distrib] using h
  have hleft : (∑ i, ∑ j, if i ∈ K then w i j else 0) ≤ (K.card : ℝ) * (1 / 48) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ.filter (fun i => i ∈ K)) => hrow i)
    simpa using h
  have hright : (∑ i, ∑ j, if j ∈ K then w i j else 0) ≤ (K.card : ℝ) * (1 / 48) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.filter (fun j => j ∈ K)) => hcol j)
    simpa using h
  have hc : (K.card : ℝ) ≤ 6 := by exact_mod_cast nearbyPaths_card_le s p
  linarith

end DirectedCycles
