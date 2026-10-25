module

public import DirectedCycles.LocalFirstExitSegment
public import DirectedCycles.LocalGlobalSubgroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A returning power segment with all binary products in its containing
set constructs an actual global cyclic subgroup. No infinite power domain
is assumed. -/
theorem PowerSegment.period_isGlobalSubgroup {u : G} {d : ℕ} (p : L.PowerSegment u d)
    (hd : 0 < d) (hperiod : p.power d = L.one) {A : Set G}
    (hmem : ∀ n < d, p.power n ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y) :
    L.IsGlobalSubgroup {x | ∃ n < d, p.power n = x} := by
  refine ⟨⟨0,hd,p.zero⟩,?_,?_⟩
  · rintro x ⟨n,hn,rfl⟩
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0,hd,by rw [p.zero,L.inv_one]⟩
    · have hnd : n+(d-n) = d := by omega
      have hm := p.add (n := n) (m := d-n) (by omega)
      rw [hnd,hperiod] at hm
      exact ⟨d-n,by omega,L.right_inverse_unique hm⟩
  · rintro x ⟨i,hi,rfl⟩ y ⟨j,hj,rfl⟩
    by_cases hs : i+j < d
    · exact ⟨p.power (i+j),⟨i+j,hs,rfl⟩,p.add hs.le⟩
    · have hi0 : 0 < i := by omega
      have hsplit : (d-i)+(i+j-d) = j := by omega
      have hsum : i+(d-i) = d := by omega
      have hab := p.add (n := i) (m := d-i) (by omega)
      rw [hsum,hperiod] at hab
      have hbc := p.add (n := d-i) (m := i+j-d) (by omega)
      rw [hsplit] at hbc
      obtain ⟨z,hz⟩ := hdom (p.power i) (hmem i hi) (p.power j) (hmem j hj)
      have he : p.power (i+j-d) = z := L.assoc hab hbc (L.one_mul _) hz
      exact ⟨z,⟨i+j-d,by omega,he⟩,hz⟩

/-- In an NSS region a genuine positive returning segment is trivial. -/
theorem PowerSegment.eq_one_of_period {A : Set G} (hNSS : L.IsNSS A)
    {u : G} {d : ℕ} (p : L.PowerSegment u d) (hd : 0 < d)
    (hperiod : p.power d = L.one) (hmem : ∀ n < d, p.power n ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y) : u = L.one := by
  by_cases hd1 : d = 1
  · subst d
    exact (p.one le_rfl).symm.trans hperiod
  · have hsub : {x | ∃ n < d, p.power n = x} ⊆ A := by
      rintro x ⟨n,hn,rfl⟩
      exact hmem n hn
    exact hNSS _ (p.period_isGlobalSubgroup L hd hperiod hmem hdom) hsub ⟨1,by omega,p.one (by omega)⟩

/-- Repeated values strictly before first exit would construct a nontrivial
global subgroup in A; NSS therefore proves injectivity of the whole prefix. -/
theorem PowerSegment.injective_prefix (hc : L.Cancellative) {A : Set G}
    (hNSS : L.IsNSS A) {u : G} (hu : u ≠ L.one) {N : ℕ}
    (p : L.PowerSegment u N) (hmem : ∀ n < N, p.power n ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y) :
    Set.InjOn p.power {n : ℕ | n < N} := by
  have strict : ∀ i j : ℕ, i < j → j < N → p.power i ≠ p.power j := by
    intro i j hij hjN he
    have hd : 0 < j-i := by omega
    have hsum : i+(j-i) = j := by omega
    have hab := p.add (n := i) (m := j-i) (by omega)
    rw [hsum,← he] at hab
    have hperiod : p.power (j-i) = L.one := hc.left_cancel hab (L.mul_one _)
    let q : L.PowerSegment u (j-i) := ⟨p.power,fun n hn => p.product n (by omega)⟩
    exact hu (q.eq_one_of_period L hNSS hd hperiod (fun n hn => hmem n (by omega)) hdom)
  intro i hi j hj he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact strict i j h hj he
  · exact strict j i h hi he.symm
end LocalGroupAlgebra
end DirectedCycles
