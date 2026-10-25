module

public import DirectedCycles.EmbeddedWalkExpansion
public import DirectedCycles.ReturnPathFamily

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The geometric end of the return-walk argument. Disjoint non-a
paths and the proved coordinate descriptions imply the precise collision
alternatives required by walk expansion. -/
theorem return_cycle_expansion {G I : Type*} [Group G] {R : Digraph G}
    (S : I → I → Set G) (root : I) (a : G) (C : Cycle R)
    (hclosed : C.ClosedUnderGenerator a) (t : I → G) (Q₀ : Set I)
    (ht : ∀ z ∈ Q₀, z ≠ root → t z = a)
    (isA : Fin C.length → Prop)
    (P : ∀ i, SimplePath (VoltageDigraph S)
      (C.vertex i,root) (C.vertex (finRotate C.length i),root))
    (hroot : ∀ i z, z ∈ (P i).vertices.dropLast → z.2 = root → z.1 = C.vertex i)
    (ha : ∀ i, isA i → ∀ z ∈ (P i).vertices.dropLast, z.1 = C.vertex i ∧ z.2 ∈ Q₀)
    (hn : ∀ i, ¬ isA i → ∀ z ∈ (P i).vertices.dropLast,
      z.1 = C.vertex i ∨ z.1 = C.vertex (finRotate C.length i)*(t z.2)⁻¹)
    (hdisjoint : ∀ i j, i ≠ j → ¬ isA i → ¬ isA j →
      (P i).vertices.Disjoint (P j).vertices) :
    ∃ L : Cycle (VoltageDigraph S), C.length ≤ L.length := by
  classical
  let f : G ↪ G × I := ⟨fun x => (x,root),fun _ _ he => congrArg Prod.fst he⟩
  apply embedded_walk_expansion C a hclosed f P
  intro i j z hi hj
  by_cases hij : i = j
  · exact Or.inl (congrArg C.vertex hij)
  by_cases hz : z.2 = root
  · exact Or.inl ((hroot i z hi hz).symm.trans (hroot j z hj hz))
  by_cases hai : isA i
  · obtain ⟨hxi,hzi⟩ := ha i hai z hi
    by_cases haj : isA j
    · exact Or.inl (hxi.symm.trans (ha j haj z hj).1)
    · rcases hn j haj z hj with he | he
      · exact Or.inl (hxi.symm.trans he)
      · have hh : C.vertex (finRotate C.length j)*(t z.2)⁻¹ = C.vertex i := he.symm.trans hxi
        rw [ht z.2 hzi hz] at hh
        exact Or.inr (Or.inr (Or.inl (mul_inv_eq_iff_eq_mul.mp hh)))
  · by_cases haj : isA j
    · obtain ⟨hxj,hzj⟩ := ha j haj z hj
      rcases hn i hai z hi with he | he
      · exact Or.inl (he.symm.trans hxj)
      · have hh : C.vertex (finRotate C.length i)*(t z.2)⁻¹ = C.vertex j := he.symm.trans hxj
        rw [ht z.2 hzj hz] at hh
        exact Or.inr (Or.inr (Or.inr (mul_inv_eq_iff_eq_mul.mp hh)))
    · exact (List.disjoint_left.mp (hdisjoint i j hij hai haj)
        (List.mem_of_mem_dropLast hi) (List.mem_of_mem_dropLast hj)).elim

end DirectedCycles
