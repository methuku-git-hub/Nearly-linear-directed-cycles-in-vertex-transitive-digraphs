import DirectedCycles.LocalQuotientMinimalLift
import DirectedCycles.LocalQuadrupledFirstExit
import DirectedCycles.LocalDivision

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} [Finite G] {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- A nonidentity point of the actual quotient image has a least-escape
lift with a positive first exit and certified fourfold power segment. Source
NSS proves positivity; no NSS assumption on the quotient is used. -/
theorem exists_minimal_lift_first_exit (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {B : Finset G} (hB : IsLocalFiniteApproximateGroup L K B)
    (hNSS : L.IsNSS (B : Set G)) {y : D.Carrier} (hy : y ∈ D.finiteImage B)
    (hy1 : y ≠ D.algebra.one) :
    ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧ x.val ≠ L.one ∧
      (∀ z : D.small, z.val ∈ B → D.project z = y → L.escapeNorm (B : Set G) x.val ≤ L.escapeNorm (B : Set G) z.val) ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∃ p : L.PowerSegment x.val (4*N),
        (∀ n < N, p.power n ∈ B) ∧ p.power N ∉ B ∧
        L.escapeNorm (B : Set G) x.val = 1/(N : ℝ) ∧
        (∀ n ≤ 4*N, p.power n ∈ L.wordPower (B : Set G) 8) := by
  obtain ⟨x,hx,hxy,hx1,hmin⟩ := D.exists_nontrivial_minimal_lift B hy hy1
  have hnonneg := L.escapeNorm_nonneg hB.one_mem x.val
  have hnonzero : L.escapeNorm (B : Set G) x.val ≠ 0 := fun he =>
    hx1 ((L.finite_nss_iff_escapeNorm (hd.cancellative L hr) hB.one_mem).1 hNSS x.val he)
  obtain ⟨N,hN,p,hp⟩ := local_approximate_quadrupled_first_exit L hB hx (lt_of_le_of_ne hnonneg hnonzero.symm)
  exact ⟨x,hx,hxy,hx1,hmin,N,hN,p,hp⟩
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
