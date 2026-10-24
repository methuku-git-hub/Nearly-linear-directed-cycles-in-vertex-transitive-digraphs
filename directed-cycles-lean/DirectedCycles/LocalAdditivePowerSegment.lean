import DirectedCycles.LocalPowerSegment
import DirectedCycles.LocalProductSplits

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A finite additive power table gives all-bracketings products, not merely
one recursively chosen bracketing. -/
theorem product_replicate_of_add {u : G} {N : ℕ} (p : ℕ → G)
    (h0 : p 0 = L.one) (h1 : 1 ≤ N → p 1 = u)
    (hadd : ∀ n m, n+m ≤ N → L.mulRel (p n) (p m) (p (n+m))) :
    ∀ n ≤ N, L.Product (List.replicate n u) (p n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n = 0
    · subst n; simpa only [h0,List.replicate_zero] using (Product.nil (L := L))
    by_cases hn1 : n = 1
    · subst n; simpa only [h1 hn,List.replicate_one] using (Product.singleton (L := L) u)
    apply (L.product_iff_finite_splits (by simp only [List.length_replicate]; omega)).2
    intro k hk hk'
    simp only [List.length_replicate] at hk'
    have hsum : k.val+(n-k.val) = n := by omega
    refine ⟨p k.val,p (n-k.val),?_,?_,?_⟩
    · simpa only [List.take_replicate,Nat.min_eq_left hk'.le] using ih k.val hk' (by omega)
    · simpa only [List.drop_replicate] using ih (n-k.val) (by omega) (by omega)
    · simpa only [hsum] using hadd k.val (n-k.val) (by omega)

/-- Constructor for finite power segments from their actual addition table. -/
def PowerSegment.of_add {u : G} {N : ℕ} (p : ℕ → G)
    (h0 : p 0 = L.one) (h1 : 1 ≤ N → p 1 = u)
    (hadd : ∀ n m, n+m ≤ N → L.mulRel (p n) (p m) (p (n+m))) :
    L.PowerSegment u N := ⟨p,L.product_replicate_of_add p h0 h1 hadd⟩
end LocalGroupAlgebra
end DirectedCycles
