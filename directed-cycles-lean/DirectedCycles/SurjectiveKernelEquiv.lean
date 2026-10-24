import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
namespace DirectedCycles

/-- Two surjective maps with exactly the same equality relation have
canonically equivalent targets. All inverse choices are justified by the
given surjectivity proofs. -/
noncomputable def surjectiveKernelEquiv {X Y Z : Type*} (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : ∀ x y : X, f x = f y ↔ g x = g y) : Y ≃ Z where
  toFun y := g (Classical.choose (hf y))
  invFun z := f (Classical.choose (hg z))
  left_inv y := by
    have he : g (Classical.choose (hg (g (Classical.choose (hf y))))) =
        g (Classical.choose (hf y)) := Classical.choose_spec (hg _)
    exact ((hker _ _).2 he).trans (Classical.choose_spec (hf y))
  right_inv z := by
    have he : f (Classical.choose (hf (f (Classical.choose (hg z))))) =
        f (Classical.choose (hg z)) := Classical.choose_spec (hf _)
    exact ((hker _ _).1 he).trans (Classical.choose_spec (hg z))

theorem surjectiveKernelEquiv_apply {X Y Z : Type*} (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : ∀ x y : X, f x = f y ↔ g x = g y) (x : X) :
    surjectiveKernelEquiv f g hf hg hker (f x) = g x :=
  (hker _ _).1 (Classical.choose_spec (hf (f x)))
end DirectedCycles
