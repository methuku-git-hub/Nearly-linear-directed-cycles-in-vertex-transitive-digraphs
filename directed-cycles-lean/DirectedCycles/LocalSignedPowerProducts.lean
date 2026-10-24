import DirectedCycles.LocalSignedPowers
import DirectedCycles.LocalAdditivePowerSegment

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} {L : LocalGroupAlgebra G} {u : G} {N : ℕ}

/-- Every bounded repeated signed power is an actual all-bracketings product,
constructed from its finite signed addition table. -/
theorem PowerSegment.signedPower_product (p : L.PowerSegment u N)
    (hd : L.DivisionClosed) (hr : L.Reversible) (k : ℤ) (n : ℕ)
    (hkn : k.natAbs*n ≤ N) :
    L.Product (List.replicate n (p.signedPower k)) (p.signedPower (k*(n : ℤ))) := by
  let f : ℕ → G := fun j => p.signedPower (k*(j : ℤ))
  have hb : ∀ j ≤ n, (k*(j : ℤ)).natAbs ≤ N := by
    intro j hj
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left k.natAbs hj).trans hkn
  have h0 : f 0 = L.one := by simp only [f,Nat.cast_zero,mul_zero,p.signedPower_zero]
  have h1 : 1 ≤ n → f 1 = p.signedPower k := by
    intro _
    simp only [f,Nat.cast_one,_root_.mul_one]
  have hadd : ∀ a b, a+b ≤ n → L.mulRel (f a) (f b) (f (a+b)) := by
    intro a b hab
    have hm := p.signedPower_add hd hr (k*(a : ℤ)) (k*(b : ℤ))
      (hb a (by omega)) (hb b (by omega)) (by simpa only [Nat.cast_add,mul_add] using hb (a+b) hab)
    simpa only [f,Nat.cast_add,mul_add] using hm
  let q := PowerSegment.of_add L f h0 h1 hadd
  exact q.product n le_rfl
end LocalGroupAlgebra
end DirectedCycles
