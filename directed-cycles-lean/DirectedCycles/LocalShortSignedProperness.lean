import DirectedCycles.LocalSignedPowers
import DirectedCycles.LocalPowerPeriod

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem PowerSegment.short_signed_return {A : Set G} (hNSS : L.IsNSS A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y) {u : G} (hu : u ≠ L.one)
    {N M : ℕ} (p : L.PowerSegment u M) (hNM : N ≤ M)
    (hprev : ∀ n < N, p.power n ∈ A) (k : ℤ) (hk : k.natAbs < N)
    (hreturn : p.signedPower k = L.one) : k = 0 := by
  have hpower : p.power k.natAbs = L.one := by
    unfold PowerSegment.signedPower at hreturn
    split_ifs at hreturn with h
    · exact hreturn
    · have hh := congrArg L.inv hreturn
      simpa only [L.inv_inv,L.inv_one] using hh
  by_contra hk0
  have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
  let q : L.PowerSegment u k.natAbs := ⟨p.power,fun n hn => p.product n (by omega)⟩
  exact hu (q.eq_one_of_period L hNSS hpos hpower (fun n hn => hprev n (by omega)) hdom)

/-- Properness of a sufficiently short signed interval is proved from the
actual finite period obstruction. It does not require a global embedding. -/
theorem PowerSegment.short_signed_injective (hd : L.DivisionClosed) (hr : L.Reversible)
    {A : Set G} (hNSS : L.IsNSS A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y) {u : G} (hu : u ≠ L.one)
    {N M m : ℕ} (p : L.PowerSegment u M) (hNM : N ≤ M)
    (hprev : ∀ n < N, p.power n ∈ A) (hm : 2*m < N) :
    Set.InjOn p.signedPower {k : ℤ | k.natAbs ≤ m} := by
  intro a ha b hb he
  have hab : (a + -b).natAbs < N := by
    have hh := Int.natAbs_add_le a (-b)
    simp only [Int.natAbs_neg] at hh
    change a.natAbs ≤ m at ha
    change b.natAbs ≤ m at hb
    omega
  have hp := p.signedPower_add hd hr a (-b) (by change a.natAbs ≤ m at ha; omega)
    (by rw [Int.natAbs_neg]; change b.natAbs ≤ m at hb; omega) (by omega)
  rw [p.signedPower_neg,he] at hp
  have hreturn := L.unique hp (L.mul_inv (p.signedPower b))
  have hz := p.short_signed_return L hNSS hdom hu hNM hprev (a + -b) hab hreturn
  omega
end LocalGroupAlgebra
end DirectedCycles
