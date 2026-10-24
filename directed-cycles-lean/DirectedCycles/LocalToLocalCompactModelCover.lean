import DirectedCycles.SmoothLocalDifferenceCells
import DirectedCycles.FiniteCoverRepresentatives
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalDivision
import DirectedCycles.LocalWordPowers

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H]

/-- A compact image in a smooth local model gives a genuine finite source
translate cover. Smooth local difference cells replace global translations;
all source difference domains and target relations are explicitly checked. -/
theorem local_finite_cover_of_compact_local_model (L : LocalGroupAlgebra G) (hd : L.DivisionClosed)
    (M : LocalGroupAlgebra H) (hM : LocalGroupSmoothness (E := E) M)
    (π : LocalGroupHom L M) (A B : Set G)
    (hAi : ∀ x ∈ A, L.inv x ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (C : Set H) (hC : IsCompact C) (hAC : π.toFun '' A ⊆ C)
    (V : Set H) (hV : V ∈ 𝓝 M.one) (hpre : π.toFun ⁻¹' V ⊆ B) :
    ∃ X : Finset G, (X : Set G) ⊆ A ∧ A ⊆ L.setMul (X : Set G) B := by
  classical
  let : Nonempty G := ⟨L.one⟩
  choose O hOo hOc hOdiff using fun c : H => smooth_local_difference_cell M hM c V hV
  have hcover : C ⊆ ⋃ c : H, O c := by
    intro c _
    exact Set.mem_iUnion.mpr ⟨c,hOc c⟩
  obtain ⟨F,hF⟩ := hC.elim_finite_subcover O hOo hcover
  obtain ⟨X,hX,_,hXcover⟩ := finite_cover_representatives F A
    (fun c x => π.toFun x ∈ O c) (by
      intro x hx
      obtain ⟨c,hc,hcx⟩ := Set.mem_iUnion₂.mp (hF (hAC ⟨x,hx,rfl⟩))
      exact ⟨c,hc,hcx⟩)
  refine ⟨X,hX,?_⟩
  intro x hx
  obtain ⟨y,hy,c,_,hcx,hcy⟩ := hXcover x hx
  obtain ⟨z,hz,hrel⟩ := hOdiff c (π.toFun y) hcy (π.toFun x) hcx
  obtain ⟨d,hm⟩ := hdom (L.inv y) (hAi y (hX hy)) x hx
  have hdB : d ∈ B := by
    apply hpre
    have hπ := π.map_mul hm
    rw [π.map_inv] at hπ
    change π.toFun d ∈ V
    exact (M.unique hrel hπ) ▸ hz
  exact ⟨y,hy,d,hdB,by simpa only [L.inv_inv] using hd.left hm⟩
end DirectedCycles
