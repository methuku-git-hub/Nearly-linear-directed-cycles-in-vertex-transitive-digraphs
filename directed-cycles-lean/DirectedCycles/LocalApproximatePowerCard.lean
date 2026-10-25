module

public import DirectedCycles.LocalApproximateCube

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Fintype G] {L : LocalGroupAlgebra G} {K : ℕ} {A : Finset G}

/-- The required bounded power cardinalities in a local approximate group.
The cover is reassociated only inside explicitly certified word domains. -/
theorem local_approximate_card_power (hA : IsLocalFiniteApproximateGroup L K A)
    (n : ℕ) (hn : n ≤ 12) : Nat.card (L.wordPower (A : Set G) (n+1)) ≤ K^n*A.card := by
  classical
  obtain ⟨X,hXcard,_,hX3,hcover⟩ := hA.cover
  have hsub : ∀ {m n : ℕ}, m ≤ n → n ≤ 200 →
      L.wordPower (A : Set G) m ⊆ L.wordPower (A : Set G) n :=
    fun {_ _} hmn hn => L.wordPower_subset_wordPower hA.one_mem hA.allProducts hmn hn
  induction n with
  | zero => simp only [zero_add,L.wordPower_one,Nat.card_coe_set_eq,Set.ncard_coe_finset,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have ih' := ih (by omega)
    let B := (L.wordPower (A : Set G) (n+1)).toFinset
    let R := L.wordPower (A : Set G) (n+3)
    have hRdom : L.AllProductsDefined R 3 := hA.allProducts.wordPower L (by omega : (n+3)*3 ≤ 200)
    have hAR : (A : Set G) ⊆ R := by simpa only [L.wordPower_one] using hsub (by omega : 1 ≤ n+3) (by omega)
    have hcov : L.wordPower (A : Set G) (n+2) ⊆ L.setMul (X : Set G) (B : Set G) := by
      intro z hz
      obtain ⟨a,ha,b,hb,hm⟩ := L.wordPower_add_subset (A : Set G) 2 n (by simpa only [Nat.add_comm] using hz)
      obtain ⟨x,hx,d,hd,hxd⟩ := hcover ha
      have hbR : b ∈ R := hsub (by omega : n ≤ n+3) (by omega) hb
      obtain ⟨e,he⟩ := hRdom [d,b] (by simp) (by aesop)
      have hdb := (LocalGroupAlgebra.Product.pair_iff L _ _ _).1 he
      have heB : e ∈ (B : Set G) := by
        apply Set.mem_toFinset.mpr
        rw [show n+1 = 1+n by omega,L.wordPower_add hA.allProducts (by omega : 1+n ≤ 200),L.wordPower_one]
        exact ⟨d,hd,b,hb,hdb⟩
      obtain ⟨v,hv,hxe⟩ := hRdom.triple L (hsub (by omega : 3 ≤ n+3) (by omega) (hX3 hx))
        (hAR hd) hbR hxd hdb
      have hvz : v = z := L.unique hv hm
      exact ⟨x,hx,e,heB,hvz ▸ hxe⟩
    have hBcard : B.card = Nat.card (L.wordPower (A : Set G) (n+1)) := by
      rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
    calc
      Nat.card (L.wordPower (A : Set G) (n+1+1)) ≤ Nat.card (L.setMul (X : Set G) (B : Set G)) :=
        Nat.card_le_card_of_injective (Set.inclusion hcov) (Set.inclusion_injective hcov)
      _ ≤ X.card*B.card := L.card_setMul_le X B
      _ ≤ K*(K^n*A.card) := Nat.mul_le_mul hXcard (by rw [hBcard]; exact ih')
      _ = K^(n+1)*A.card := by ring
end DirectedCycles
