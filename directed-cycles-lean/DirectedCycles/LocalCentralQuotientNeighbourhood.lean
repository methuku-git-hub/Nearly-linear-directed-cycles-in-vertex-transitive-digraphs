import DirectedCycles.LocalCentralQuotientData
import DirectedCycles.LocalExponentialWordNeighbourhood

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H]

/-- A central local set in an actual local Lie target has genuine central
quotient data on arbitrarily small open symmetric windows. The larger
congruence window and every required word domain are constructed. -/
theorem local_central_quotient_of_neighbourhoods {Q : LocalGroupAlgebra H}
    (D : LocalExponentialData (E := E) Q) (hd : Q.DivisionClosed) (hr : Q.Reversible)
    {P V S : Set H} (hP : Q.CentralLocalSet P V S)
    (hV : V ∈ 𝓝 Q.one) (hS : S ∈ 𝓝 Q.one) (U : Set H) (hU : U ∈ 𝓝 Q.one) :
    ∃ T : Q.CentralQuotientData P, IsOpen T.small ∧ T.small ⊆ U := by
  obtain ⟨B,hBo,hB1,hBi,hBsub,hBdom,hBp⟩ := D.exists_open_word_neighbourhood (V ∩ S) (Filter.inter_mem hV hS) 8
  have hP' : Q.CentralLocalSet P V B :=
    ⟨hP.one_mem,hP.inv_mem,hP.mul_mem,fun p hp x hx => hP.central p hp x (hBsub hx).2⟩
  have hBV : Q.wordPower B 8 ⊆ V := fun _ hx => (hBp 8 le_rfl hx).1
  let C := hP'.equivalenceWindow hd hr hB1 hBi hBdom hBV
  have hBnhds : B ∈ 𝓝 Q.one := hBo.mem_nhds hB1
  obtain ⟨W,hWo,hW1,hWi,hWsub,hWdom,hWp⟩ := D.exists_open_word_neighbourhood (B ∩ U) (Filter.inter_mem hBnhds hU) 3
  let T : Q.CentralQuotientData P := {
    large := B
    small := W
    small_subset := fun _ hx => (hWsub hx).1
    one_mem := hW1
    inv_mem := hWi
    domain := hWdom
    cube_subset := fun _ hx => (hWp 3 le_rfl hx).1
    equivalence := C
    relation_iff := fun _ _ => Iff.rfl }
  exact ⟨T,hWo,fun _ hx => (hWsub hx).2⟩
end DirectedCycles
