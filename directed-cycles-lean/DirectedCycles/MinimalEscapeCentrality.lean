module

public import DirectedCycles.EscapeNorm
public import Mathlib.Data.Finset.Max

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The finite minimum needed by the central-progression argument is selected
from actual nonidentity elements, with its positivity proved from NSS. -/
theorem exists_minimal_escape (A : Finset G) (hA : (1 : G) ∈ A)
    (hNSS : ∀ g : G, escapeNorm A g = 0 → g = 1)
    (hne : ∃ g ∈ A, g ≠ 1) :
    ∃ u ∈ A, u ≠ 1 ∧ 0 < escapeNorm A u ∧
      ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v := by
  classical
  have hs : (A.erase 1).Nonempty := by
    obtain ⟨g,hg,hg1⟩ := hne
    exact ⟨g,Finset.mem_erase.mpr ⟨hg1,hg⟩⟩
  obtain ⟨u,hu,hmin⟩ := (A.erase 1).exists_min_image (escapeNorm (A : Set G)) hs
  have huA := (Finset.mem_erase.mp hu).2
  have hu1 := (Finset.mem_erase.mp hu).1
  refine ⟨u,huA,hu1,?_,?_⟩
  · have h0 := escapeNorm_nonneg hA u
    have hn : escapeNorm A u ≠ 0 := fun he => hu1 (hNSS u he)
    exact lt_of_le_of_ne h0 (Ne.symm hn)
  · intro v hv hv1
    exact hmin v (Finset.mem_erase.mpr ⟨hv1,hv⟩)

/-- A commutator smaller than the least positive escape norm must be trivial.
This isolates the algebraic centrality step from the subsequent Lie-model choice
of a sufficiently small approximate subgroup. -/
theorem minimal_escape_commutes {A : Set G} (hA : 1 ∈ A)
    {u x : G} (hu : 0 < escapeNorm A u)
    (hmin : ∀ v ∈ A, v ≠ 1 → escapeNorm A u ≤ escapeNorm A v)
    {D : ℝ} (hbound : escapeNorm A (x⁻¹*u⁻¹*x*u) ≤ D*escapeNorm A x*escapeNorm A u)
    (hsmall : D*escapeNorm A x < 1) : Commute x u := by
  have hlt : escapeNorm A (x⁻¹*u⁻¹*x*u) < escapeNorm A u := by nlinarith
  have hm : x⁻¹*u⁻¹*x*u ∈ A :=
    mem_of_escapeNorm_lt_one hA (hlt.trans_le (escapeNorm_le_one hA u))
  have he : x⁻¹*u⁻¹*x*u = 1 := by
    by_contra h
    exact (not_lt_of_ge (hmin _ hm h)) hlt
  have hh := congrArg (fun z => u*x*z) he
  change x*u = u*x
  simpa [mul_assoc] using hh
end DirectedCycles
