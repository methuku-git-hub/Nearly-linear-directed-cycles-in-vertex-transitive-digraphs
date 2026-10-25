module

public import DirectedCycles.LocalUltraproductMaps
public import DirectedCycles.LocalInternalSetLogic

@[expose] public section

set_option autoImplicit false
open Filter
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G H : ι → Type*)

/-- Inverse images of internal sets under actual component maps are internal. -/
theorem localUltraMap_preimage (f : ∀ i, G i → H i) (B : ∀ i, Set (H i)) :
    localUltraMap F G H f ⁻¹' localUltraSet F H B =
      localUltraSet F G (fun i => f i ⁻¹' B i) := by
  ext x
  obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
  change localUltraMk F H (fun i => f i (a i)) ∈ localUltraSet F H B ↔ _
  simp only [localUltraMk_mem_iff,Set.mem_preimage]

/-- Images of internal sets are internal. The default representative is used
only at indices outside the eventual membership set. -/
theorem localUltraMap_image (e : ∀ i, G i) (f : ∀ i, G i → H i)
    (A : ∀ i, Set (G i)) :
    localUltraMap F G H f '' localUltraSet F G A =
      localUltraSet F H (fun i => f i '' A i) := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
    apply (localUltraMk_mem_iff F H _ _).2
    have ha := (localUltraMk_mem_iff F G A a).1 hx
    exact ha.mono fun i hi => ⟨a i,hi,rfl⟩
  · intro y hy
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
    have hb := (localUltraMk_mem_iff F H _ b).1 hy
    let a : ∀ i, G i := fun i => if h : b i ∈ f i '' A i then Classical.choose h else e i
    have ha : ∀ᶠ i in F, a i ∈ A i ∧ f i (a i) = b i := by
      filter_upwards [hb] with i hi
      dsimp only [a]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    refine ⟨localUltraMk F G a,(localUltraMk_mem_iff F G A a).2 (ha.mono fun _ h => h.1),?_⟩
    exact Quotient.sound (ha.mono fun _ h => h.2)

/-- Eventual injectivity suffices for injectivity of the reduced-product map. -/
theorem localUltraMap_injective (f : ∀ i, G i → H i)
    (hf : ∀ᶠ i in F, Function.Injective (f i)) :
    Function.Injective (localUltraMap F G H f) := by
  intro x y h
  obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
  have he : ∀ᶠ i in F, f i (a i) = f i (b i) := Quotient.exact h
  apply Quotient.sound
  filter_upwards [hf,he] with i hi hei
  exact hi hei

/-- Eventual surjectivity also suffices, with source representatives supplied
at the remaining indices. -/
theorem localUltraMap_surjective_of_eventually (e : ∀ i, G i) (f : ∀ i, G i → H i)
    (hf : ∀ᶠ i in F, Function.Surjective (f i)) :
    Function.Surjective (localUltraMap F G H f) := by
  classical
  intro y
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
  let a : ∀ i, G i := fun i => if h : ∃ a, f i a = b i then Classical.choose h else e i
  refine ⟨localUltraMk F G a,Quotient.sound ?_⟩
  filter_upwards [hf] with i hi
  have hex : ∃ a, f i a = b i := hi (b i)
  dsimp only [a]
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex
end DirectedCycles
