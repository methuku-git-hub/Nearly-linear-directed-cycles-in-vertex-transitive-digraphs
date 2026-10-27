module

public import DirectedCycles.LocalCentralQuotientData
public import DirectedCycles.LocalEscapeNorm

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- Controlled lifts of a whole tuple retain the reciprocal-length bounds
coming from actual quotient power segments. -/
theorem controlled_generator_lifts (B : Finset G) {C : ℝ} (hC : 0 ≤ C)
    (hcontrol : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm B x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B) y)
    {r : ℕ} (g : Fin r → D.Carrier) (N : Fin r → ℕ)
    (hg : ∀ i, g i ∈ D.finiteImage B)
    (hpowers : ∀ i, ∀ n ≤ N i, D.algebra.PowerIn (D.finiteImage B) (g i) n) :
    ∃ u : Fin r → D.small, ∀ i, (u i).val ∈ B ∧ D.project (u i) = g i ∧
      L.escapeNorm B (u i).val ≤ C/((N i : ℝ)+1) := by
  choose u hu hproj hbound using fun i => hcontrol (g i) (hg i)
  refine ⟨u,fun i => ⟨hu i,hproj i,?_⟩⟩
  have hh := (hbound i).trans (mul_le_mul_of_nonneg_left (D.algebra.escapeNorm_le_of_powers (hpowers i)) hC)
  simpa only [mul_one_div] using hh
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
