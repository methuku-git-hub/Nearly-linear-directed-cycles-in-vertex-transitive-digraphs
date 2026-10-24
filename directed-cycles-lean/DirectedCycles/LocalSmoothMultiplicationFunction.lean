import DirectedCycles.LocalGroupSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A function agreeing with local multiplication on its actual domain. The
arbitrary value at undefined pairs supplies no multiplication relation. -/
noncomputable def multiplicationFunction (p : G × G) : G := by
  classical
  exact if h : L.Defined p.1 p.2 then L.mul p.1 p.2 h else L.one

theorem multiplicationFunction_spec {a b : G} (h : L.Defined a b) :
    L.mulRel a b (L.multiplicationFunction (a,b)) := by
  rw [multiplicationFunction,dite_eq_left h]
  exact L.mul_spec a b h

theorem multiplicationFunction_eq {a b c : G} (h : L.mulRel a b c) :
    L.multiplicationFunction (a,b) = c :=
  L.unique (L.multiplicationFunction_spec ⟨c,h⟩) h

variable {E : Type*} [TopologicalSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G]

/-- On every actually defined pair, the chosen multiplication function is
smooth; this follows from the local smoothness axiom and functionality. -/
theorem multiplicationFunction_contMDiffAt (hL : LocalGroupSmoothness (E := E) L)
    {a b : G} (h : L.Defined a b) :
    ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ L.multiplicationFunction (a,b) := by
  obtain ⟨m,hm,hmrel⟩ := hL.smooth_mul a b h
  apply hm.congr_of_eventuallyEq
  filter_upwards [hmrel] with p hp
  exact L.multiplicationFunction_eq hp
end LocalGroupAlgebra
end DirectedCycles
