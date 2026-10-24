import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalGroupUltraproduct

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G H : ι → Type*)

/-- Actual component functions induce a function of reduced products. -/
def localUltraMap (f : ∀ i, G i → H i) : LocalUltraproduct F G → LocalUltraproduct F H :=
  Quotient.map (fun a i => f i (a i)) (by
    intro a b h
    exact h.mono fun i hi => congrArg (f i) hi)

theorem localUltraMap_surjective (f : ∀ i, G i → H i) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (localUltraMap F G H f) := by
  classical
  intro b
  induction b using Quotient.inductionOn with
  | h b =>
    choose a ha using fun i => hf i (b i)
    refine ⟨localUltraMk F G a,?_⟩
    apply Quotient.sound
    exact Filter.Eventually.of_forall ha

/-- Partial homomorphisms induce an actual partial homomorphism of reduced
products. No component product is completed outside its domain. -/
def localUltraHom (L : ∀ i, LocalGroupAlgebra (G i)) (M : ∀ i, LocalGroupAlgebra (H i))
    (f : ∀ i, LocalGroupHom (L i) (M i)) :
    LocalGroupHom (localUltraAlgebra F G L) (localUltraAlgebra F H M) where
  toFun := localUltraMap F G H (fun i => (f i).toFun)
  map_one := Quotient.sound (Filter.Eventually.of_forall fun i => (f i).map_one)
  map_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | h a => exact Quotient.sound (Filter.Eventually.of_forall fun i => (f i).map_inv (a i))
  map_mul := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a b c hm
    apply (localUltraMulRel_mk_iff F H M _ _ _).2
    have hh := (localUltraMulRel_mk_iff F G L a b c).1 hm
    exact hh.mono fun i hi => (f i).map_mul hi
end DirectedCycles
