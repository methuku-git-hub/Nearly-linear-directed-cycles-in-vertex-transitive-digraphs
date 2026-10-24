import DirectedCycles.ConjugationModule

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- Ordered iterated commutators, retained as elements of the normal subgroup. -/
def normalIteratedCommutator {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    List G → N → N
  | [], b => b
  | g::gs, b => normalConjugation N g (normalIteratedCommutator N gs b) *
      (normalIteratedCommutator N gs b)⁻¹

/-- Ordered action differences are represented by ordered group commutators. -/
theorem normalAbelianAction_difference_product {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (gs : List G) (b : N) :
    (gs.map (fun g => normalAbelianAction N g-1)).prod (normalAbelianElement N b) =
      normalAbelianElement N (normalIteratedCommutator N gs b) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change (normalAbelianAction N g-1)
      ((gs.map (fun g => normalAbelianAction N g-1)).prod (normalAbelianElement N b)) = _
    rw [ih,normalAbelianAction_difference]
    rfl

/-- Each difference raises the lower central weight by one. -/
theorem normalIteratedCommutator_mem_lower {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (gs : List G) (b : N) (i : ℕ)
    (hb : b.val ∈ lowerSeries G i) :
    (normalIteratedCommutator N gs b).val ∈ lowerSeries G (gs.length+i) := by
  induction gs with
  | nil => simpa [normalIteratedCommutator] using hb
  | cons g gs ih =>
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih
    rw [Subgroup.commutator_comm] at h
    change ⁅g,(normalIteratedCommutator N gs b).val⁆ ∈ lowerSeries G (gs.length+i+1) at h
    change ⁅g,(normalIteratedCommutator N gs b).val⁆ ∈ lowerSeries G (gs.length+1+i)
    simpa only [Nat.add_right_comm] using h

/-- Nilpotency of the ambient group kills every sufficiently long product of
conjugation differences, with no torsion restriction on the module. -/
theorem normalAbelianAction_nilpotent {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (c : ℕ) (hc : Group.nilpotencyClass G ≤ c)
    (gs : List G) (hlen : c ≤ gs.length) :
    (gs.map (fun g => normalAbelianAction N g-1)).prod = 0 := by
  ext x
  obtain ⟨b,rfl⟩ := normalAbelianElement_surjective N x
  rw [normalAbelianAction_difference_product]
  have h := normalIteratedCommutator_mem_lower N gs b 0 (Subgroup.mem_top _)
  have hbot : lowerSeries G gs.length = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (hc.trans hlen)
  simp only [Nat.add_zero,hbot,Subgroup.mem_bot] at h
  have he : normalIteratedCommutator N gs b = 1 := Subtype.ext h
  rw [he,normalAbelianElement_one]
  rfl

/-- The single-generator unipotence needed by the connector recurrence. -/
theorem normalAbelianAction_unipotent {G : Type*} [Group G] [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (c : ℕ) (hc : Group.nilpotencyClass G ≤ c) (g : G) :
    (normalAbelianAction N g-1)^c = 0 := by
  simpa using normalAbelianAction_nilpotent N c hc (List.replicate c g) (by simp)

end DirectedCycles
