module

public import DirectedCycles.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A homomorphism to an abelian group has exponent dividing e if its
values on a generating set do. -/
theorem commutative_image_exponent_of_generators {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (S : Set G) (hS : Subgroup.closure S = ⊤) (e : ℕ)
    (he : ∀ x ∈ S, f x ^ e = 1) (g : G) : f g ^ e = 1 := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact he x hx
  | one => simp
  | mul x y _ _ hx hy => simp only [map_mul, mul_pow, hx, hy, one_mul]
  | inv x _ hx => simp only [map_inv, inv_pow, hx, inv_one]

/-- Passing to the abelianization of a normal closure does not enlarge the
exponent of its conjugate generators. -/
theorem normalClosure_abelianization_exponent {G : Type*} [Group G]
    (A : Subgroup G) (e : ℕ) (he : ∀ a : A, a ^ e = 1) :
    ∀ x : Abelianization (Subgroup.normalClosure (A : Set G)), x ^ e = 1 := by
  let S := Group.conjugatesOfSet (A : Set G)
  let L := Subgroup.normalClosure (A : Set G)
  have hgen : Subgroup.closure (L.subtype ⁻¹' S) = ⊤ := Subgroup.closure_preimage_eq_top S
  have hpow : ∀ x ∈ L.subtype ⁻¹' S, (Abelianization.of x) ^ e = 1 := by
    intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    change g * a * g⁻¹ = x.val at hg
    have ha1 : a ^ e = 1 := congrArg Subtype.val (he ⟨a, ha⟩)
    have hx1 : x.val ^ e = 1 := by rw [← hg, conj_pow, ha1, mul_one, mul_inv_cancel]
    have hxL : x ^ e = 1 := Subtype.ext hx1
    rw [← map_pow, hxL, map_one]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator L) x
  exact commutative_image_exponent_of_generators Abelianization.of (L.subtype ⁻¹' S) hgen e hpow g

/-- The finite stabilizer case used in Lemma 3.9. -/
theorem normalClosure_abelianization_card_exponent {G : Type*} [Group G]
    (A : Subgroup G) :
    ∀ x : Abelianization (Subgroup.normalClosure (A : Set G)), x ^ Nat.card A = 1 :=
  normalClosure_abelianization_exponent A (Nat.card A) (fun _ => pow_card_eq_one')

end DirectedCycles
