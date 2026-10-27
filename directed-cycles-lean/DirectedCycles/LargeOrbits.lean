module

public import DirectedCycles.LargeOrbitConstruction
public import DirectedCycles.LargeOrbitThresholds

@[expose] public section

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- Manuscript Theorem 3.6, with a uniform threshold depending only on the
exponent and the induced stabilizer bound. The construction also proves the
statement without the unnecessary upper restriction on the exponent. -/
theorem large_normal_orbits {ell : ℝ} (hell : 0 < ell) (B : ℕ) (hB : 1 ≤ B) :
    ∃ N : ℕ, ∀ (G V : Type*) [Group G] [Fintype G] [Fintype V] [MulAction G V],
      ∀ (H : Subgroup G) [H.Normal]
        [Fintype (Quotient (MulAction.orbitRel H V))]
        [DecidableEq (Quotient (MulAction.orbitRel H V))],
      ∀ (D : Digraph V), Connected D →
      (∀ (g : G) x y, D (g • x) (g • y) ↔ D x y) →
      (∀ x y : V, ∃ g : G, g • x = y) → N ≤ Fintype.card V →
      ∀ m : ℕ,
      (∀ a : Quotient (MulAction.orbitRel H V), Fintype.card {x : V // Quotient.mk'' x = a} = m) →
      (Fintype.card V : ℝ) ^ (4 * ell) ≤ m →
      (∀ x y, MulAction.orbitRel H V x y →
        ∃ P : SimplePath (fun u v => D u v ∨ D v u) x y,
          (P.length : ℝ) ≤ (Fintype.card V : ℝ) ^ ell) →
      letI := normalOrbitAction (V := V) H
      (∀ a : Quotient (MulAction.orbitRel H V),
        Fintype.card (MulAction.stabilizer (PermutationImage G (Quotient (MulAction.orbitRel H V))) a) ≤ B) →
      ∃ C : Cycle D, (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (1 - 3 * ell) ≤ C.length := by
  obtain ⟨N, hN⟩ := large_orbit_thresholds hell B hB
  refine ⟨N, ?_⟩
  intro G V _ _ _ _ H _ _ _ D hconnected hD ht hn m hm hmb hdiam
  let : MulAction G (Quotient (MulAction.orbitRel H V)) := normalOrbitAction H
  intro hstab
  obtain ⟨hn2, hp2, hsampling, hpower⟩ := hN (Fintype.card V) hn
  have hm2 : 2 ≤ m := by exact_mod_cast hp2.trans hmb
  have hlarge : 192 * degreeBudget (Fintype.card V) B * (connectionSize (Fintype.card V) ell) ^ 2 ≤ m := by
    exact_mod_cast hsampling.trans hmb
  obtain ⟨C, hC⟩ := large_normal_orbits_finite H D hconnected hD ht hn2 ell hell.le B m hB hm hm2 hdiam hlarge hstab
  refine ⟨C, ?_⟩
  exact (sampling_bound_to_power (by omega) (by unfold connectionSize; omega) hpower).trans hC

end DirectedCycles
