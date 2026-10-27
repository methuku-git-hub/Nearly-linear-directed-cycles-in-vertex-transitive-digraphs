module

public import DirectedCycles.LocalMultiplicativeGermUniqueness
public import DirectedCycles.LocalGroupAlgebra

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {H : Type*}

/-- Agreement near zero determines actual local relation curves throughout
the common parameter interval. A selected product is used only at pairs for
which one of the supplied multiplication relations proves it is defined. -/
theorem local_relation_curve_eq_of_eventually_eq (Q : LocalGroupAlgebra H)
    (f g : ℝ → H) (h0 : f 0 = g 0) {r s : ℝ}
    (hf : ∀ a b : ℝ, |a|+|b| ≤ r → Q.mulRel (f a) (f b) (f (a+b)))
    (hg : ∀ a b : ℝ, |a|+|b| ≤ s → Q.mulRel (g a) (g b) (g (a+b)))
    (hnear : f =ᶠ[𝓝 (0 : ℝ)] g) (t : ℝ) (htr : |t| ≤ r) (hts : |t| ≤ s) : f t = g t := by
  classical
  let μ : H × H → H := fun p => if h : Q.Defined p.1 p.2 then Q.mul p.1 p.2 h else Q.one
  have hμ : ∀ x y z : H, Q.mulRel x y z → μ (x,y) = z := by
    intro x y z h
    dsimp only [μ]
    rw [dite_eq_left (show Q.Defined x y from ⟨z,h⟩)]
    exact Q.unique (Q.mul_spec _ _ _) h
  exact local_multiplicative_eq_of_eventually_eq μ f g h0
    (fun a b h => (hμ _ _ _ (hf a b h)).symm) (fun a b h => (hμ _ _ _ (hg a b h)).symm)
    hnear t htr hts
end DirectedCycles
