import DirectedCycles.CycleConnectivity

set_option autoImplicit false
namespace DirectedCycles
namespace Cycle
variable {G I : Type*} [Group G] {D : Digraph (G × I)}

def UnusedIndices (C : Cycle D) := {i : I // i ∉ Set.range (fun j => (C.vertex j).2)}

instance unusedIndices_finite [Finite I] (C : Cycle D) : Finite C.UnusedIndices :=
  inferInstanceAs (Finite {i : I // i ∉ Set.range (fun j => (C.vertex j).2)})

/-- Contract all left translates of the cycle simultaneously. The `none`
index is its contracted orbit; all unused orbit indices remain separate. -/
noncomputable def contractProjection (C : Cycle D) (x : G × I) : G × Option C.UnusedIndices := by
  classical
  exact if hi : x.2 ∈ Set.range (fun j => (C.vertex j).2) then
    (x.1*((C.vertex hi.choose).1)⁻¹,none)
  else (x.1,some ⟨x.2,hi⟩)

theorem contractProjection_cycle (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2)) (g : G) (j : Fin C.length) :
    C.contractProjection (g*(C.vertex j).1,(C.vertex j).2) = (g,none) := by
  classical
  unfold contractProjection
  split_ifs with h
  · have hj : h.choose = j := hinj h.choose_spec
    simp only [hj,mul_inv_cancel_right]
  · exact (h ⟨j,rfl⟩).elim

theorem contractProjection_unused (C : Cycle D) (g : G) (i : C.UnusedIndices) :
    C.contractProjection (g,i.val) = (g,some i) := by
  classical
  unfold contractProjection
  rw [dite_eq_right i.property]
  rfl

theorem contractProjection_eq_none (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2)) (x : G × I) (g : G) :
    C.contractProjection x = (g,none) ↔
      ∃ j, x = (g*(C.vertex j).1,(C.vertex j).2) := by
  classical
  constructor
  · intro he
    unfold contractProjection at he
    split_ifs at he with hi
    · have hg := congrArg Prod.fst he
      have hfirst : x.1 = g*(C.vertex hi.choose).1 := by
        have hm := congrArg (fun z => z*(C.vertex hi.choose).1) hg
        simpa only [inv_mul_cancel_right] using hm
      exact ⟨hi.choose,Prod.ext hfirst hi.choose_spec.symm⟩
    · have hh := congrArg Prod.snd he
      cases hh
  · rintro ⟨j,rfl⟩
    exact C.contractProjection_cycle hinj g j

theorem contractProjection_eq_some (C : Cycle D) (x : G × I) (g : G) (i : C.UnusedIndices) :
    C.contractProjection x = (g,some i) ↔ x = (g,i.val) := by
  classical
  constructor
  · intro he
    unfold contractProjection at he
    split_ifs at he with hi
    · have hh := congrArg Prod.snd he
      cases hh
    · have hg := congrArg Prod.fst he
      have hi' : (⟨x.2,hi⟩ : C.UnusedIndices) = i := Option.some.inj (congrArg Prod.snd he)
      exact Prod.ext hg (congrArg Subtype.val hi')
  · rintro rfl
    exact C.contractProjection_unused g i

theorem contractProjection_surjective (C : Cycle D)
    (hinj : Function.Injective (fun j => (C.vertex j).2)) : Function.Surjective C.contractProjection := by
  rintro ⟨g,i⟩
  cases i with
  | none =>
    let j : Fin C.length := ⟨0,by have := C.two_le; omega⟩
    exact ⟨(g*(C.vertex j).1,(C.vertex j).2),C.contractProjection_cycle hinj g j⟩
  | some i => exact ⟨(g,i.val),C.contractProjection_unused g i⟩

theorem contractProjection_translate (C : Cycle D) (g : G) (x : G × I) :
    C.contractProjection (g*x.1,x.2) =
      (g*(C.contractProjection x).1,(C.contractProjection x).2) := by
  classical
  unfold contractProjection
  split_ifs <;> simp only [mul_assoc]

end Cycle
end DirectedCycles
