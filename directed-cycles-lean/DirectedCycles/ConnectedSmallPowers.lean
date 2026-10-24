import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- A nontrivial connected T1 group has nonidentity elements in every open
identity neighbourhood. -/
theorem exists_ne_one_in_open {H : Type*} [Group H] [TopologicalSpace H]
    [PreconnectedSpace H] [T1Space H] [Nontrivial H]
    {W : Set H} (hWo : IsOpen W) (hW1 : (1 : H) ∈ W) : ∃ x ∈ W, x ≠ 1 := by
  by_contra h
  have hh : ∀ x ∈ W, x = (1 : H) := by simpa using h
  have he : W = {1} := by
    ext x
    constructor
    · exact fun hx => hh x hx
    · intro hx
      simpa only [Set.mem_singleton_iff.mp hx] using hW1
  have hsing : IsOpen ({1} : Set H) := he ▸ hWo
  have hclopen : IsClopen ({1} : Set H) := ⟨isClosed_singleton,hsing⟩
  have huniv : ({1} : Set H) = Set.univ := hclopen.eq_univ ⟨1,rfl⟩
  obtain ⟨x,hx⟩ := exists_ne (1 : H)
  exact hx (by have hm : x ∈ ({1} : Set H) := huniv.symm ▸ Set.mem_univ x; exact hm)

/-- A surjective model map with a small inverse neighbourhood supplies
nonidentity elements with arbitrarily long power segments in the source set. -/
theorem exists_long_power_segment_of_connected_model {S H : Type*} [Group S] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [PreconnectedSpace H] [T1Space H] [Nontrivial H]
    (π : S →* H) (hπ : Function.Surjective π) (B : Set S) (W : Set H)
    (hWo : IsOpen W) (hW1 : (1 : H) ∈ W) (hsmall : π ⁻¹' W ⊆ B) (M : ℕ) :
    ∃ z : S, z ≠ 1 ∧ ∀ n ≤ M, z^n ∈ B := by
  let V : Set H := ⋂ j : Fin (M+1), {x | x^(j.val) ∈ W}
  have hVo : IsOpen V := isOpen_iInter_of_finite (fun j => hWo.preimage (continuous_pow j.val))
  have hV1 : (1 : H) ∈ V := by
    apply Set.mem_iInter.mpr
    intro j
    simpa using hW1
  obtain ⟨y,hy,hy1⟩ := exists_ne_one_in_open hVo hV1
  obtain ⟨z,hz⟩ := hπ y
  refine ⟨z,?_,?_⟩
  · intro he
    apply hy1
    rw [← hz,he,map_one]
  · intro n hn
    apply hsmall
    change π (z^n) ∈ W
    rw [map_pow,hz]
    exact Set.mem_iInter.mp hy ⟨n,by omega⟩
end DirectedCycles
