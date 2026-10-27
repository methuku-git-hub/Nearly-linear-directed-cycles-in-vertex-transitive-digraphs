module

public import DirectedCycles.LocalPowerSegment
public import DirectedCycles.LocalDivision

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
namespace PowerSegment
variable {G : Type*} {L : LocalGroupAlgebra G} {u : G} {N : ℕ}

/-- Signed values of an actual finite power segment. Algebraic laws are only
asserted when all relevant indices stay in the certified segment. -/
def signedPower (p : L.PowerSegment u N) (k : ℤ) : G :=
  if 0 ≤ k then p.power k.natAbs else L.inv (p.power k.natAbs)

theorem signedPower_nat (p : L.PowerSegment u N) (n : ℕ) :
    p.signedPower (n : ℤ) = p.power n := by simp [signedPower]

theorem signedPower_neg_nat (p : L.PowerSegment u N) (n : ℕ) :
    p.signedPower (-(n : ℤ)) = L.inv (p.power n) := by
  by_cases hn : n = 0
  · subst n
    simp [signedPower,p.zero,L.inv_one]
  · have hn' : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    simp only [signedPower,ite_eq_right hn',Int.natAbs_neg,Int.natAbs_natCast]

theorem signedPower_zero (p : L.PowerSegment u N) : p.signedPower 0 = L.one := by
  simpa only [Int.natCast_zero,p.zero] using p.signedPower_nat 0

theorem signedPower_neg (p : L.PowerSegment u N) (k : ℤ) :
    p.signedPower (-k) = L.inv (p.signedPower k) := by
  rcases Int.eq_nat_or_neg k with ⟨n,rfl | rfl⟩
  · rw [p.signedPower_neg_nat,p.signedPower_nat]
  · rw [neg_neg,p.signedPower_nat,p.signedPower_neg_nat,L.inv_inv]

/-- The signed addition law uses division and reversal to construct every
mixed-sign product; it assumes no multiplication outside the finite interval. -/
theorem signedPower_add (p : L.PowerSegment u N) (hd : L.DivisionClosed)
    (hr : L.Reversible) (a b : ℤ) (ha : a.natAbs ≤ N) (hb : b.natAbs ≤ N)
    (hab : (a+b).natAbs ≤ N) :
    L.mulRel (p.signedPower a) (p.signedPower b) (p.signedPower (a+b)) := by
  have mixed : ∀ m n : ℕ, m ≤ N → n ≤ N →
      L.mulRel (p.power m) (L.inv (p.power n)) (p.signedPower ((m : ℤ)-n)) := by
    intro m n hm hn
    by_cases hnm : n ≤ m
    · have he : (m : ℤ)-n = ((m-n : ℕ) : ℤ) := by omega
      rw [he,p.signedPower_nat]
      have h := hd.right (p.add (n := m-n) (m := n) (by omega))
      simpa only [Nat.sub_add_cancel hnm] using h
    · have he : (m : ℤ)-n = -((n-m : ℕ) : ℤ) := by omega
      rw [he,p.signedPower_neg_nat]
      have h := hr (hd.right (p.add (n := n-m) (m := m) (by omega)))
      simpa only [Nat.sub_add_cancel (by omega : m ≤ n),L.inv_inv] using h
  rcases Int.eq_nat_or_neg a with ⟨m,rfl | rfl⟩ <;>
    rcases Int.eq_nat_or_neg b with ⟨n,rfl | rfl⟩
  · rw [← Nat.cast_add,p.signedPower_nat,p.signedPower_nat,p.signedPower_nat]
    apply p.add
    simpa only [← Nat.cast_add,Int.natAbs_natCast] using hab
  · simpa only [p.signedPower_nat,p.signedPower_neg_nat,sub_eq_add_neg] using
      mixed m n (by simpa using ha) (by simpa using hb)
  · have hm : m ≤ N := by simpa using ha
    have hn : n ≤ N := by simpa using hb
    by_cases hmn : m ≤ n
    · have he' : -(m : ℤ)+n = ((n-m : ℕ) : ℤ) := by omega
      rw [p.signedPower_neg_nat,p.signedPower_nat,he',p.signedPower_nat]
      have hh := hd.left (p.add (n := m) (m := n-m) (by omega))
      simpa only [Nat.add_sub_cancel' hmn] using hh
    · have hh := hr (hd.left (p.add (n := n) (m := m-n) (by omega)))
      have he' : -(m : ℤ)+n = -((m-n : ℕ) : ℤ) := by omega
      rw [p.signedPower_neg_nat,p.signedPower_nat,he',p.signedPower_neg_nat]
      simpa only [Nat.add_sub_cancel' (by omega : n ≤ m),L.inv_inv] using hh
  · rw [← neg_add,← Nat.cast_add,p.signedPower_neg_nat,p.signedPower_neg_nat,p.signedPower_neg_nat]
    have hmn : m+n ≤ N := by
      simpa only [← neg_add,← Nat.cast_add,Int.natAbs_neg,Int.natAbs_natCast] using hab
    have hh := hr (p.add (n := n) (m := m) (by omega))
    simpa only [Nat.add_comm n m] using hh
end PowerSegment
end LocalGroupAlgebra
end DirectedCycles
