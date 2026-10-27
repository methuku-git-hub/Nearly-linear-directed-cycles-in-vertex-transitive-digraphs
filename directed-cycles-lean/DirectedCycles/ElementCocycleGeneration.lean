module

public import DirectedCycles.ElementCocycle

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- The commutator cocycle values additively generate B/B'. -/
theorem elementCocycle_generates {G : Type*} [Group G] (a : G) :
    AddSubgroup.closure (Set.range (elementCocycle a)) = ⊤ := by
  let B := elementCommutators a
  let W := AddSubgroup.closure (Set.range (elementCocycle a))
  let U : Subgroup G := {
    carrier := {x | ∃ hx : x ∈ B, normalAbelianElement B ⟨x,hx⟩ ∈ W}
    one_mem' := ⟨B.one_mem,by change normalAbelianElement B 1 ∈ W; rw [normalAbelianElement_one]; exact W.zero_mem⟩
    mul_mem' := by
      rintro x y ⟨hx,hxW⟩ ⟨hy,hyW⟩
      refine ⟨B.mul_mem hx hy,?_⟩
      change normalAbelianElement B ((⟨x,hx⟩ : B)*⟨y,hy⟩) ∈ W
      rw [normalAbelianElement_mul]
      exact W.add_mem hxW hyW
    inv_mem' := by
      rintro x ⟨hx,hxW⟩
      refine ⟨B.inv_mem hx,?_⟩
      change normalAbelianElement B (⟨x,hx⟩ : B)⁻¹ ∈ W
      rw [normalAbelianElement_inv]
      exact W.neg_mem hxW }
  have hBU : B ≤ U := by
    apply U.closure_le.mpr
    rintro x ⟨g,rfl⟩
    exact ⟨mem_elementCommutators a g,AddSubgroup.subset_closure ⟨g,rfl⟩⟩
  apply top_unique
  intro v _
  obtain ⟨b,rfl⟩ := normalAbelianElement_surjective B v
  obtain ⟨_,hb⟩ := hBU b.property
  exact hb

end DirectedCycles
