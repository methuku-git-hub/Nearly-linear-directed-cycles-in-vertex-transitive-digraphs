module

public import DirectedCycles.PrimeCharacters
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommPiCoprod

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A common prime index set can be used for the Sylow decomposition of
several finite nilpotent groups. Primes absent from a group's order contribute
trivial factors. -/
noncomputable def finiteSylowModel (G : Type*) [Group G] [Finite G] [Group.IsNilpotent G]
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hcontains : (Nat.card G).primeFactors ⊆ s) :
    (∀ p : s, (default : Sylow p.val G)) ≃* G := by
  classical
  let P : ∀ p : s, Sylow p.val G := fun _ => default
  have hcomm : Pairwise fun p q : s => ∀ x y : G, x ∈ P p → y ∈ P q → Commute x y := by
    intro p q hpq
    let : Fact p.val.Prime := ⟨hs p.val p.property⟩
    let : Fact q.val.Prime := ⟨hs q.val q.property⟩
    apply Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
    exact IsPGroup.disjoint_of_ne p.val q.val (fun h => hpq (Subtype.ext h)) _ _
      (P p).isPGroup' (P q).isPGroup'
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  let : Fintype G := Fintype.ofFinite G
  let : ∀ p : s, Fintype (P p) := fun _ => Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    intro p q hpq
    let : Fact p.val.Prime := ⟨hs p.val p.property⟩
    let : Fact q.val.Prime := ⟨hs q.val q.property⟩
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p.val q.val (fun h => hpq (Subtype.ext h)) _ _
      (P p).isPGroup' (P q).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (∀ p : s, P p) = ∏ p : s, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : s, p.val ^ (Nat.card G).factorization p.val := by
        congr 1 with p
        let : Fact p.val.Prime := ⟨hs p.val p.property⟩
        exact Sylow.card_eq_multiplicity (P p)
      _ = ∏ p ∈ s, p ^ (Nat.card G).factorization p :=
        (Finset.prod_finset_coe (fun p : ℕ => p ^ (Nat.card G).factorization p) s)
      _ = ∏ p ∈ (Nat.card G).primeFactors, p ^ (Nat.card G).factorization p := by
        symm
        apply Finset.prod_subset hcontains
        intro p _ hp
        have hz : (Nat.card G).factorization p = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          exact hp (Nat.mem_primeFactors.mpr ⟨hs p ‹p ∈ s›,hd,Nat.card_pos.ne'⟩)
        rw [hz,pow_zero]
      _ = Nat.card G := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

/-- The explicitly constructed common-prime Sylow model is bijective. -/
theorem finiteSylowModel_bijective (G : Type*) [Group G] [Finite G] [Group.IsNilpotent G]
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hcontains : (Nat.card G).primeFactors ⊆ s) :
    Function.Bijective (finiteSylowModel G s hs hcontains) :=
  (finiteSylowModel G s hs hcontains).bijective

end DirectedCycles
