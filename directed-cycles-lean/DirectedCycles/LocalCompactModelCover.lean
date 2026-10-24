import DirectedCycles.FiniteCoverRepresentatives
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalDivision
import DirectedCycles.LocalWordPowers
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Precompact model image and an inner model preimage give a finite local
translate cover. The translating elements are chosen from the actual source
set, and every source relative difference has a verified binary domain. -/
theorem local_finite_cover_of_compact_model (L : LocalGroupAlgebra G) (hd : L.DivisionClosed)
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H)) (A B : Set G)
    (hAi : ∀ x ∈ A, L.inv x ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (C : Set H) (hC : IsCompact C) (hAC : π.toFun '' A ⊆ C)
    (V : Set H) (hV : V ∈ 𝓝 (1 : H)) (hpre : π.toFun ⁻¹' V ⊆ B) :
    ∃ X : Finset G, (X : Set G) ⊆ A ∧ A ⊆ L.setMul (X : Set G) B := by
  classical
  let : Nonempty G := ⟨L.one⟩
  obtain ⟨D,hDn,_,hDi,hDD⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  let O := interior D
  have hO : IsOpen O := isOpen_interior
  have hO1 : (1 : H) ∈ O := mem_interior_iff_mem_nhds.mpr hDn
  let cells : H → Set H := fun g => (fun y : H => g*y) '' O
  have hcellso : ∀ g, IsOpen (cells g) := fun g => isOpenMap_mul_left g O hO
  have hcover : C ⊆ ⋃ g : H, cells g := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,1,hO1,mul_one x⟩
  obtain ⟨F,hF⟩ := hC.elim_finite_subcover cells hcellso hcover
  obtain ⟨X,hX,_,hXcover⟩ := finite_cover_representatives F A
    (fun g x => π.toFun x ∈ cells g) (by
      intro x hx
      obtain ⟨g,hg,hgx⟩ := Set.mem_iUnion₂.mp (hF (hAC ⟨x,hx,rfl⟩))
      exact ⟨g,hg,hgx⟩)
  refine ⟨X,hX,?_⟩
  intro x hx
  obtain ⟨y,hy,g,_,hgx,hgy⟩ := hXcover x hx
  obtain ⟨wx,hwx,hex⟩ := hgx
  obtain ⟨wy,hwy,hey⟩ := hgy
  have hwxi : wx ∈ D := interior_subset hwx
  have hwyi : wy ∈ D := interior_subset hwy
  have hwyinv : wy⁻¹ ∈ D := by
    rw [← hDi]
    exact Set.mem_inv.mpr (by simpa only [inv_inv] using hwyi)
  have hdiff : (π.toFun y)⁻¹*π.toFun x ∈ V := by
    have he : (π.toFun y)⁻¹*π.toFun x = wy⁻¹*wx := by rw [← hey,← hex]; group
    rw [he]
    exact hDD (Set.mem_mul.mpr ⟨wy⁻¹,hwyinv,wx,hwxi,rfl⟩)
  obtain ⟨d,hm⟩ := hdom (L.inv y) (hAi y (hX hy)) x hx
  have hdB : d ∈ B := by
    apply hpre
    have hπ := π.map_mul hm
    rw [π.map_inv] at hπ
    change (π.toFun y)⁻¹*π.toFun x = π.toFun d at hπ
    change π.toFun d ∈ V
    exact hπ ▸ hdiff
  exact ⟨y,hy,d,hdB,by simpa only [L.inv_inv] using hd.left hm⟩
end DirectedCycles
