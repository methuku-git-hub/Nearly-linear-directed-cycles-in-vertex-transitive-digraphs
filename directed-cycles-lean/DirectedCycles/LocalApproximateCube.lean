module

public import DirectedCycles.LocalFiniteProductCard
public import DirectedCycles.LocalProductCompression
public import DirectedCycles.LocalTripleProducts
public import DirectedCycles.LocalWordPowerMonotonicity

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {K : ℕ} {A : Finset G}

/-- The cubic cardinal estimate uses the actual covering set and only nine
letters of the given 200-letter domain. No global set associativity is used. -/
theorem local_approximate_card_cube (hA : IsLocalFiniteApproximateGroup L K A) :
    Nat.card (L.wordPower (A : Set G) 3) ≤ K^2*A.card := by
  classical
  obtain ⟨X,hXcard,_,hX3,hcover⟩ := hA.cover
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hB : (B : Set G) = L.wordPower (A : Set G) 2 := Set.coe_toFinset _
  have hA3 : (A : Set G) ⊆ L.wordPower (A : Set G) 3 := by
    have hh := L.wordPower_subset_wordPower hA.one_mem hA.allProducts
      (by omega : 1 ≤ 3) (by omega : 3 ≤ 200)
    simpa only [L.wordPower_one] using hh
  have hdom3 := hA.allProducts.wordPower L (by omega : 3*3 ≤ 200)
  have hsub : L.wordPower (A : Set G) 3 ⊆ L.setMul (X : Set G) (B : Set G) := by
    intro z hz
    obtain ⟨ab,hab,b,hb,hm⟩ := L.wordPower_add_subset (A : Set G) 2 1 hz
    have hbA : b ∈ (A : Set G) := by simpa only [L.wordPower_one] using hb
    obtain ⟨x,hx,d,hd,hxd⟩ := hcover hab
    obtain ⟨e,he⟩ := hA.allProducts [d,b] (by simp) (by aesop)
    have hdb := (LocalGroupAlgebra.Product.pair_iff L d b e).1 he
    have heB : e ∈ (B : Set G) := by
      rw [hB]
      exact ⟨[d,b],rfl,by aesop,he⟩
    obtain ⟨v,hv,hxe⟩ := hdom3.triple L (hX3 hx) (hA3 hd) (hA3 hbA) hxd hdb
    have hvz : v = z := L.unique hv hm
    exact ⟨x,hx,e,heB,hvz ▸ hxe⟩
  have hcard := Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  calc
    Nat.card (L.wordPower (A : Set G) 3) ≤ Nat.card (L.setMul (X : Set G) (B : Set G)) := hcard
    _ ≤ X.card*B.card := L.card_setMul_le X B
    _ ≤ K*(K*A.card) := Nat.mul_le_mul hXcard (by rw [hBcard]; exact local_approximate_doubling hA)
    _ = K^2*A.card := by ring
end DirectedCycles
