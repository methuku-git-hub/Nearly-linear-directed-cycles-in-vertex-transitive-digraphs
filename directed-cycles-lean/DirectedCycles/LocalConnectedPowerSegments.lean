import DirectedCycles.LocalModelPowerLifting
import DirectedCycles.ConnectedSmallPowers

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- A nontrivial connected target and a locally onto model supply arbitrary
finite genuine power segments in the local source. All source product domains
are constructed by the preceding lifting theorem. -/
theorem exists_local_long_power_segment_of_connected_model {G H : Type*}
    (L : LocalGroupAlgebra G) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [PreconnectedSpace H] [T1Space H] [Nontrivial H]
    (A : Set G) (hA : L.one ∈ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L (LocalGroupAlgebra.ofGroup H)) (W : Set H)
    (hWo : IsOpen W) (hW1 : (1 : H) ∈ W)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A)
    (hthick : ∀ y ∈ W, ∃ x, π.toFun x = y) (M : ℕ) :
    ∃ z : G, z ≠ L.one ∧ ∀ n ≤ M, L.PowerIn A z n := by
  let V : Set H := ⋂ j : Fin (M+2), {x | x^j.val ∈ W}
  have hVo : IsOpen V := isOpen_iInter_of_finite (fun j => hWo.preimage (continuous_pow j.val))
  have hV1 : (1 : H) ∈ V := by
    apply Set.mem_iInter.mpr
    intro j
    simpa using hW1
  obtain ⟨y,hy,hy1⟩ := exists_ne_one_in_open hVo hV1
  have hyW : y ∈ W := by simpa using Set.mem_iInter.mp hy ⟨1,by omega⟩
  obtain ⟨z,hz⟩ := hthick y hyW
  have hzA : z ∈ A := hsmall z (hz.symm ▸ hyW)
  refine ⟨z,?_,L.powerIn_of_model_powers A hA hdom π W hsmall hzA M ?_⟩
  · intro he
    apply hy1
    rw [← hz,he,π.map_one]
    rfl
  · intro n hn
    rw [hz]
    exact Set.mem_iInter.mp hy ⟨n,by omega⟩
end DirectedCycles
