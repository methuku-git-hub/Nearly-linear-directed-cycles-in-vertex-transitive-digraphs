module

public import DirectedCycles.LocalIteratedGeneratorCommutators

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem GeneratorCommutators.mono {S T : Set G} (hST : S ⊆ T) {n : ℕ} {x : G}
    (hx : L.GeneratorCommutators S n x) : L.GeneratorCommutators T n x := by
  induction hx with
  | base h => exact .base (hST h)
  | step _ hy hp ih => exact .step ih (hST hy) hp

/-- Adding the identity to the generators creates no new nonidentity
iterated commutator, even in a local group. -/
theorem generatorCommutators_insert_one (hr : L.Reversible) {S : Set G} {n : ℕ} {x : G}
    (hx : L.GeneratorCommutators (insert L.one S) n x) :
    x = L.one ∨ L.GeneratorCommutators S n x := by
  induction hx with
  | base hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (.base hx)
  | @step n x y z _ hy hp ih =>
    rcases ih with rfl | hx
    · exact Or.inl (L.commutator_product_eq_one hr ⟨y,L.one_mul y,L.mul_one y⟩ hp)
    · rcases hy with rfl | hy
      · exact Or.inl (L.commutator_product_eq_one hr ⟨x,L.mul_one x,L.one_mul x⟩ hp)
      · exact Or.inr (.step hx hy hp)

theorem generatorCommutators_vanish_insert_one (hr : L.Reversible) {S : Set G} (c : ℕ)
    (hc : ∀ x, L.GeneratorCommutators S c x → x = L.one) :
    ∀ x, L.GeneratorCommutators (insert L.one S) c x → x = L.one := by
  intro x hx
  exact (L.generatorCommutators_insert_one hr hx).elim id (hc x)
end LocalGroupAlgebra
end DirectedCycles
