import DirectedCycles.LocalQuotientMinimalLift
import DirectedCycles.LocalEscapeNSS
import DirectedCycles.LocalDivision

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- Finite minimization converts the uniform least-lift bound into an
actual escape-controlled lift of every point of the quotient image. -/
theorem escape_controlled_lifts_of_minimal_bound (B : Finset G) {C : ℝ}
    (hbound : ∀ x : D.small, x.val ∈ B →
      (∀ z : D.small, z.val ∈ B → D.project z = D.project x →
        L.escapeNorm (B : Set G) x.val ≤ L.escapeNorm (B : Set G) z.val) →
      L.escapeNorm (B : Set G) x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B : Set D.Carrier) (D.project x)) :
    ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm (B : Set G) x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B : Set D.Carrier) y := by
  intro y hy
  obtain ⟨x,hx,hxy,hmin⟩ := D.exists_minimal_lift B hy
  refine ⟨x,hx,hxy,?_⟩
  rw [← hxy]
  exact hbound x hx (fun z hz hzx => hmin z hz (hzx.trans hxy))

/-- Escape-controlled lifting proves NSS for the actual finite quotient
image. Quotient NSS is a conclusion of this theorem, never an input. -/
theorem nss_of_escape_controlled_lifts [Finite G]
    (hd : L.DivisionClosed) (hr : L.Reversible) (B : Finset G)
    (hB1 : L.one ∈ B) (hNSS : L.IsNSS (B : Set G)) {C : ℝ}
    (hlift : ∀ y ∈ D.finiteImage B, ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      L.escapeNorm (B : Set G) x.val ≤ C*D.algebra.escapeNorm (D.finiteImage B : Set D.Carrier) y) :
    D.algebra.IsNSS (D.finiteImage B : Set D.Carrier) := by
  classical
  have hq1 : D.algebra.one ∈ D.finiteImage B :=
    Finset.mem_image.mpr ⟨⟨L.one,D.one_mem⟩,by simpa only [Finset.mem_subtype] using hB1,D.projectionHom.map_one⟩
  apply (D.algebra.finite_nss_iff_escapeNorm (D.algebra_cancellative hd hr) hq1).2
  intro y hy
  have hymem := D.algebra.mem_of_escapeNorm_lt_one hq1 (by rw [hy]; norm_num)
  obtain ⟨x,_,hxy,hbound⟩ := hlift y hymem
  rw [hy,mul_zero] at hbound
  have hxzero := le_antisymm hbound (L.escapeNorm_nonneg hB1 x.val)
  have hx1 := (L.finite_nss_iff_escapeNorm (hd.cancellative L hr) hB1).1 hNSS x.val hxzero
  have he : x = (L.restrict D.small D.one_mem D.inv_mem).one := Subtype.ext hx1
  rw [← hxy,he]
  exact D.projectionHom.map_one
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
