module

public import DirectedCycles.PrimeCharacters
public import Mathlib.GroupTheory.NoncommPiCoprod

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A homomorphism between groups of distinct prime-power exponents is trivial. -/
theorem hom_between_distinct_pgroups {G H : Type*} [Group G] [Group H]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hG : IsPGroup p G) (hH : IsPGroup q H) (f : G →* H) (x : G) : f x = 1 := by
  obtain ⟨a,ha⟩ := hG x
  obtain ⟨b,hb⟩ := hH (f x)
  have hp : orderOf (f x) ∣ p^a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow,ha,map_one]
  have hq : orderOf (f x) ∣ q^b := orderOf_dvd_of_pow_eq_one hb
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_pow_primes _ _ Fact.out Fact.out hpq) hp hq

/-- A homomorphism from a product of distinct primary groups to one primary
group depends only on the matching coordinate. -/
theorem primary_product_hom_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → Type*} [∀ i, Group (B i)] {G : Type*} [Group G]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hB : ∀ i, IsPGroup (p i) (B i)) (j : ι) (hG : IsPGroup (p j) G)
    (f : (∀ i, B i) →* G) (x : ∀ i, B i) :
    f x = f (Pi.mulSingle j (x j)) := by
  classical
  let f' : (∀ i, B i) →* G := (f.comp (MonoidHom.mulSingle B j)).comp (Pi.evalMonoidHom B j)
  have he : f = f' := by
    apply MonoidHom.pi_ext
    intro i y
    by_cases hij : i = j
    · subst i
      simp [f']
    · let : Fact (p i).Prime := ⟨hp i⟩
      let : Fact (p j).Prime := ⟨hp j⟩
      have hh := hom_between_distinct_pgroups (p i) (p j) (fun h => hij (hinj h))
        (hB i) hG (f.comp (MonoidHom.mulSingle B i)) y
      simpa [f',hij] using hh
  exact congrArg (fun g : (∀ i, B i) →* G => g x) he

end DirectedCycles
