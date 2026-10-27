module

public import DirectedCycles.LocalUltraproductProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Existence of a fully defined fixed word transfers, including its value. -/
theorem localUltra_exists_product_iff (l : List (∀ i, G i)) :
    (∃ x, (localUltraAlgebra F G L).Product (l.map (localUltraMk F G)) x) ↔
      ∀ᶠ i in F, ∃ x, (L i).Product (l.map (fun a => a i)) x := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨a,rfl⟩ := Quotient.exists_rep x
    exact ((localUltraProduct_mk_iff F G L l a).1 hx).mono fun _ hi => ⟨_,hi⟩
  · intro h
    let a : ∀ i, G i := fun i => if hi : ∃ x, (L i).Product (l.map (fun a => a i)) x
      then Classical.choose hi else (L i).one
    refine ⟨localUltraMk F G a,(localUltraProduct_mk_iff F G L l a).2 ?_⟩
    filter_upwards [h] with i hi
    dsimp only [a]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
end DirectedCycles
