import DirectedCycles.LocalQuotientMinimalLift
import DirectedCycles.LocalCorrectedPowerSegment

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- A genuine corrected segment staying in the source through the old first
exit gives a lift with strictly smaller escape norm. Both quotient equality
and the strict reciprocal comparison are proved here. -/
theorem corrected_lift_strict_improvement (hd : L.DivisionClosed)
    {B : Set G} (hB : B ⊆ D.small) {g h c : G}
    (hg : g ∈ B) (hc : c ∈ P) (hprod : L.mulRel c g h)
    {M : ℕ} (hM : 0 < M) (p : L.PowerSegment h M)
    (hpB : ∀ n ≤ M, p.power n ∈ B)
    (hnorm : L.escapeNorm B g = 1/(M : ℝ)) :
    ∃ x : D.small, x.val ∈ B ∧ D.project x = D.project ⟨g,hB hg⟩ ∧
      L.escapeNorm B x.val < L.escapeNorm B g := by
  have hh : h ∈ B := (p.one hM) ▸ hpB 1 hM
  refine ⟨⟨h,hB hh⟩,hh,?_,?_⟩
  · apply (D.project_eq_iff _ _).2
    exact (D.relation_iff _ _).2 ⟨c,hc,hd.right hprod⟩
  · have hn := L.escapeNorm_le_of_powers (fun n hn => ⟨p.power n,hpB n hn,p.product n hn⟩)
    rw [hnorm]
    exact hn.trans_lt (one_div_lt_one_div_of_lt (by exact_mod_cast hM) (by linarith : (M : ℝ) < (M : ℝ)+1))

/-- In particular the corrected segment is impossible for the actual
least-escape lift in a finite quotient fibre. -/
theorem minimal_lift_excludes_corrected_segment (hd : L.DivisionClosed)
    (B : Finset G) (hB : (B : Set G) ⊆ D.small) (g : D.small)
    (hg : g.val ∈ B)
    (hmin : ∀ z : D.small, z.val ∈ B → D.project z = D.project g →
      L.escapeNorm (B : Set G) g.val ≤ L.escapeNorm (B : Set G) z.val)
    {h c : G} (hc : c ∈ P) (hprod : L.mulRel c g.val h)
    {M : ℕ} (hM : 0 < M) (p : L.PowerSegment h M)
    (hpB : ∀ n ≤ M, p.power n ∈ B)
    (hnorm : L.escapeNorm (B : Set G) g.val = 1/(M : ℝ)) : False := by
  obtain ⟨x,hx,he,hlt⟩ := D.corrected_lift_strict_improvement hd hB hg hc hprod hM p hpB hnorm
  exact (not_lt_of_ge (hmin x hx he)) hlt
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
