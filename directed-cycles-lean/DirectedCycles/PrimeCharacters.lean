module

public import DirectedCycles.ElementNormalClosure
public import Mathlib.Algebra.Module.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Homomorphisms from G to the additive prime field, viewed as a vector space.
The domain is allowed to be noncommutative. -/
abbrev PrimeCharacters (G : Type*) [Group G] (p : ℕ) := Additive G →+ ZMod p

instance primeCharacters_finite (G : Type*) [Group G] [Finite G] (p : ℕ) [NeZero p] :
    Finite (PrimeCharacters G p) :=
  Finite.of_injective (fun f : PrimeCharacters G p => (f : Additive G → ZMod p)) DFunLike.coe_injective

noncomputable def primeCharacterDimension (G : Type*) [Group G] (p : ℕ) [Fact p.Prime] : ℕ :=
  Module.finrank (ZMod p) (PrimeCharacters G p)

/-- Evaluation on a generating set determines a character. -/
theorem primeCharacter_eq_of_generators {G : Type*} [Group G] {p : ℕ}
    (S : Set G) (hS : Subgroup.closure S = ⊤) (f g : PrimeCharacters G p)
    (he : ∀ x ∈ S, f (Additive.ofMul x) = g (Additive.ofMul x)) : f = g := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply MonoidHom.eq_of_eqOn_dense hS
  intro x hx
  exact congrArg Multiplicative.ofAdd (he x hx)

/-- The space of prime characters has dimension at most the generator rank. -/
theorem primeCharacterDimension_le_rank {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] : primeCharacterDimension G p ≤ Group.rank G := by
  classical
  obtain ⟨S,hcard,hS⟩ := Group.rank_spec G
  let ev : PrimeCharacters G p →ₗ[ZMod p] (S → ZMod p) := {
    toFun := fun f x => f (Additive.ofMul x.val)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hi : Function.Injective ev := by
    intro f g he
    apply primeCharacter_eq_of_generators (S : Set G) hS f g
    intro x hx
    exact congrFun he ⟨x,hx⟩
  have h := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [primeCharacterDimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_coe,smul_eq_mul,mul_one,hcard] using h

/-- Every prime divisor of a finite nilpotent group yields a nonzero prime
character. A proved normal subgroup of prime index supplies the quotient. -/
theorem nilpotent_prime_character {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (p : ℕ) [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ f : PrimeCharacters G p, f ≠ 0 := by
  obtain ⟨H,hindex,hH⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  let : H.Normal := hH
  have hcard : Nat.card (G ⧸ H) = p := hindex
  have hzcard : Nat.card (Multiplicative (ZMod p)) = p := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  let e : G ⧸ H ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcard hzcard
  let f : G →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' H)
  have hs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective H)
  refine ⟨f.toAdditiveLeft,?_⟩
  intro he
  obtain ⟨x,hx⟩ := hs (Multiplicative.ofAdd (1 : ZMod p))
  have hv := congrArg (fun g : PrimeCharacters G p => g (Additive.ofMul x)) he
  change (f x).toAdd = 0 at hv
  rw [hx] at hv
  exact one_ne_zero hv

/-- A nonzero character is nonzero on at least one available generator. -/
theorem nonzero_primeCharacter_on_generator {G : Type*} [Group G] {p : ℕ}
    (S : Set G) (hS : Subgroup.closure S = ⊤) (f : PrimeCharacters G p) (hf : f ≠ 0) :
    ∃ a ∈ S, f (Additive.ofMul a) ≠ 0 := by
  by_contra he
  apply hf
  apply primeCharacter_eq_of_generators S hS f 0
  intro x hx
  by_contra hne
  exact he ⟨x,hx,hne⟩

end DirectedCycles
