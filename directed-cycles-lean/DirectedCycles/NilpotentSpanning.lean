module

public import DirectedCycles.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.LinearMap.End

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The elementary nilpotent-ideal spanning argument, stated for a submodule
of endomorphisms. It applies without finite generation or torsion restrictions. -/
theorem nilpotent_operator_spanning {V : Type*} [AddCommGroup V]
    (I : Submodule ℤ (Module.End ℤ V)) (W : Submodule ℤ V) (D : ℕ)
    (hstable : I • W ≤ W) (hspan : W ⊔ I • (⊤ : Submodule ℤ V) = ⊤)
    (hnil : (I ^ D) • (⊤ : Submodule ℤ V) = ⊥) : W = ⊤ := by
  have hpow : ∀ n : ℕ, W ⊔ (I ^ n) • (⊤ : Submodule ℤ V) = ⊤ := by
    intro n
    induction n with
    | zero => simp only [Submodule.pow_zero, Submodule.one_smul, sup_top_eq]
    | succ n ih =>
      apply top_le_iff.mp
      calc (⊤ : Submodule ℤ V) = W ⊔ I • (⊤ : Submodule ℤ V) := hspan.symm
           _ = W ⊔ I • (W ⊔ (I ^ n) • (⊤ : Submodule ℤ V)) := by rw [ih]
           _ = W ⊔ (I • W ⊔ I • ((I ^ n) • (⊤ : Submodule ℤ V))) := by rw [Submodule.smul_sup]
           _ ≤ W ⊔ I • ((I ^ n) • (⊤ : Submodule ℤ V)) := by
             exact sup_le (le_sup_left) (sup_le (hstable.trans le_sup_left) le_sup_right)
           _ = W ⊔ (I ^ (n+1)) • (⊤ : Submodule ℤ V) := by
             by_cases hn : n = 0
             · subst n
               simp only [Submodule.pow_zero, Submodule.one_smul, Nat.zero_add, Submodule.pow_one]
             · rw [Submodule.pow_succ' I hn]
               exact congrArg (fun P : Submodule ℤ V => W ⊔ P) (Submodule.smul_assoc I (I ^ n) ⊤).symm
  simpa only [hnil, sup_bot_eq] using hpow D

/-- If mV lies in the image of a nilpotent endomorphism, iterating gives
m^D V=0. This is the exponent step in the auxiliary-group index bound. -/
theorem exponent_of_nilpotent_range {V : Type*} [AddCommGroup V]
    (N : Module.End ℤ V) (m D : ℕ) (hnil : N ^ D = 0)
    (hspan : ∀ v : V, ∃ w : V, m • v = N w) : ∀ v : V, m ^ D • v = 0 := by
  have hp : ∀ n : ℕ, ∀ v : V, ∃ w : V, m ^ n • v = (N ^ n) w := by
    intro n
    induction n with
    | zero => intro v; exact ⟨v, by simp⟩
    | succ n ih =>
      intro v
      obtain ⟨w,hw⟩ := ih v
      obtain ⟨u,hu⟩ := hspan w
      refine ⟨u, ?_⟩
      rw [pow_succ', mul_smul, hw, ← map_nsmul, hu, pow_succ, Module.End.mul_apply]
  intro v
  obtain ⟨w,hw⟩ := hp D v
  simpa only [hnil, LinearMap.zero_apply] using hw

end DirectedCycles
