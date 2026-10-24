import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalEscapeNorm

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- Each point of a finite projected set has an actual least-escape lift in
that set. This is finite minimization over the exact quotient fibre. -/
theorem exists_minimal_lift (B : Finset G) {y : D.Carrier} (hy : y ∈ D.finiteImage B) :
    ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧
      ∀ z : D.small, z.val ∈ B → D.project z = y → L.escapeNorm (B : Set G) x.val ≤ L.escapeNorm (B : Set G) z.val := by
  classical
  let S : Finset D.small := (B.subtype (· ∈ D.small)).filter (fun x => D.project x = y)
  have hS : S.Nonempty := by
    change y ∈ (B.subtype (· ∈ D.small)).image D.project at hy
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hy
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,he⟩⟩
  obtain ⟨x,hx,hmin⟩ := S.exists_min_image (fun x => L.escapeNorm (B : Set G) x.val) hS
  have hx' := Finset.mem_filter.mp hx
  refine ⟨x,by simpa only [Finset.mem_subtype] using hx'.1,hx'.2,?_⟩
  intro z hz hzy
  apply hmin z
  exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_subtype] using hz,hzy⟩

/-- A nonidentity projected point has a nonidentity least-escape lift. -/
theorem exists_nontrivial_minimal_lift (B : Finset G) {y : D.Carrier}
    (hy : y ∈ D.finiteImage B) (hy1 : y ≠ D.algebra.one) :
    ∃ x : D.small, x.val ∈ B ∧ D.project x = y ∧ x.val ≠ L.one ∧
      ∀ z : D.small, z.val ∈ B → D.project z = y → L.escapeNorm (B : Set G) x.val ≤ L.escapeNorm (B : Set G) z.val := by
  obtain ⟨x,hx,hxy,hmin⟩ := D.exists_minimal_lift B hy
  refine ⟨x,hx,hxy,?_,hmin⟩
  intro he
  have hx1 : x = (L.restrict D.small D.one_mem D.inv_mem).one := Subtype.ext he
  apply hy1
  rw [← hxy,hx1]
  exact D.projectionHom.map_one
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
