module

public import DirectedCycles.LocalCommutingPowerSegments
public import DirectedCycles.LocalSignedPowerProducts
public import DirectedCycles.LocalSignedPowerCommutation

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A bounded arithmetic subsequence of signed powers is itself an actual
finite power segment. -/
def PowerSegment.signedMultipleSegment {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hd : L.DivisionClosed) (hr : L.Reversible) (k : ℤ) (m : ℕ) (hkm : k.natAbs*m ≤ N) :
    L.PowerSegment (p.signedPower k) m where
  power j := p.signedPower (k*(j : ℤ))
  product j hj := p.signedPower_product hd hr k j ((Nat.mul_le_mul_left k.natAbs hj).trans hkm)

/-- Correcting a local generator by a bounded signed central power gives a
certified segment of corrected powers. The exponent bound explicitly supplies
all powers used in the correction. -/
theorem PowerSegment.corrected_segment (hd : L.DivisionClosed) (hr : L.Reversible)
    {A : Set G} (hi : ∀ x ∈ A, L.inv x ∈ A) (hdom : L.AllProductsDefined A 4)
    {g u : G} (hu : u ∈ A) {M N : ℕ} (hM : 1 ≤ M)
    (p : L.PowerSegment g M) (q : L.PowerSegment u N)
    (hpA : ∀ n ≤ M, p.power n ∈ A) (hqA : ∀ n ≤ N, q.power n ∈ A)
    (hgu : L.Commute g u) (k : ℤ) (hk : k.natAbs*M ≤ N) :
    ∃ h : G, L.mulRel g (q.signedPower (-k)) h ∧ ∃ s : L.PowerSegment h M,
      (∀ n ≤ M, L.mulRel (p.power n) (q.signedPower (-k*(n : ℤ))) (s.power n)) ∧
      (∀ n ≤ M, s.power n ∈ L.wordPower A 2) := by
  have hg : g ∈ A := (p.one hM) ▸ hpA 1 hM
  have hkN : (-k).natAbs ≤ N := by
    rw [Int.natAbs_neg]
    nlinarith
  let t := q.signedMultipleSegment L hd hr (-k) M (by simpa only [Int.natAbs_neg] using hk)
  have htA : ∀ n ≤ M, t.power n ∈ A := by
    intro n hn
    have hkn : (-k*(n : ℤ)).natAbs ≤ N := by
      simp only [Int.natAbs_mul,Int.natAbs_neg,Int.natAbs_natCast]
      exact (Nat.mul_le_mul_left k.natAbs hn).trans hk
    change q.signedPower (-k*(n : ℤ)) ∈ A
    dsimp only [PowerSegment.signedPower]
    split_ifs
    · exact hqA _ hkn
    · exact hi _ (hqA _ hkn)
  have hgt : L.Commute g (q.signedPower (-k)) := q.commute_signedPower L hd hi
    (hdom.mono L (Set.Subset.refl _) (by omega : 3 ≤ 4)) hu hg hgu (-k) hkN
    (fun n hn => hqA n (hn.trans hkN))
  exact p.product_segment L hdom hM t hpA htA hgt
end LocalGroupAlgebra
end DirectedCycles
