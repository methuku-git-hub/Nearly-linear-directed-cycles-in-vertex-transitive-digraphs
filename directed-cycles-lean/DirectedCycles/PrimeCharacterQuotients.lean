import DirectedCycles.PrimeCharacters
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false
namespace DirectedCycles

def primeCharacterPullback {G H : Type*} [Group G] [Group H] (p : ℕ) (q : G →* H) :
    PrimeCharacters H p →ₗ[ZMod p] PrimeCharacters G p where
  toFun f := f.comp q.toAdditive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeCharacterPullback_injective {G H : Type*} [Group G] [Group H]
    (p : ℕ) (q : G →* H) (hq : Function.Surjective q) :
    Function.Injective (primeCharacterPullback p q) := by
  intro f g he
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y,hy⟩ := hq x.toMul
  have h := congrArg (fun f : PrimeCharacters G p => f (Additive.ofMul y)) he
  change f (Additive.ofMul (q y)) = g (Additive.ofMul (q y)) at h
  simpa only [hy,ofMul_toMul] using h

theorem primeCharacterDimension_quotient_le {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (p : ℕ) [Fact p.Prime]
    (q : G →* H) (hq : Function.Surjective q) :
    primeCharacterDimension H p ≤ primeCharacterDimension G p :=
  LinearMap.finrank_le_finrank_of_injective (primeCharacterPullback_injective p q hq)

def primeCharacterEval {G : Type*} [Group G] (p : ℕ) (a : G) :
    PrimeCharacters G p →ₗ[ZMod p] ZMod p where
  toFun f := f (Additive.ofMul a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Characters of the normal-closure quotient are exactly the characters
vanishing on the selected label. -/
theorem primeCharacter_range_eq_eval_ker {G : Type*} [Group G] (p : ℕ) (a : G) :
    (primeCharacterPullback p (QuotientGroup.mk' (elementClosure a))).range =
      (primeCharacterEval p a).ker := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    change g (Additive.ofMul (QuotientGroup.mk' (elementClosure a) a)) = 0
    have ha : QuotientGroup.mk' (elementClosure a) a = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_elementClosure a)
    rw [ha]
    exact map_zero g
  · intro hf
    change f (Additive.ofMul a) = 0 at hf
    let fm := f.toMultiplicativeRight
    have hker : elementClosure a ≤ fm.ker := by
      rw [elementClosure_eq_normalClosure]
      apply Subgroup.normalClosure_le_normal
      intro x hx
      have he : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact congrArg Multiplicative.ofAdd hf
    let g := (QuotientGroup.lift (elementClosure a) fm hker).toAdditiveLeft
    exact ⟨g,AddMonoidHom.ext (fun _ => rfl)⟩

theorem primeCharacterEval_surjective {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (a : G) (f : PrimeCharacters G p) (hf : f (Additive.ofMul a) ≠ 0) :
    Function.Surjective (primeCharacterEval p a) := by
  intro x
  refine ⟨(x/f (Additive.ofMul a)) • f,?_⟩
  change (x/f (Additive.ofMul a))*f (Additive.ofMul a) = x
  exact div_mul_cancel₀ x hf

/-- The selected prime dimension decreases by exactly one. -/
theorem primeCharacterDimension_normalClosure_drop {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (a : G) (f : PrimeCharacters G p)
    (hf : f (Additive.ofMul a) ≠ 0) :
    primeCharacterDimension (G ⧸ elementClosure a) p + 1 = primeCharacterDimension G p := by
  have hpull := LinearMap.finrank_range_of_inj
    (primeCharacterPullback_injective p (QuotientGroup.mk' (elementClosure a))
      (QuotientGroup.mk'_surjective (elementClosure a)))
  rw [primeCharacter_range_eq_eval_ker] at hpull
  have h := (primeCharacterEval p a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (primeCharacterEval_surjective p a f hf),
    finrank_top,Module.finrank_self,hpull] at h
  simpa only [primeCharacterDimension,Nat.add_comm] using h

end DirectedCycles
