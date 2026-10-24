import DirectedCycles.LocalPowerExtension
import DirectedCycles.LocalPowerSegmentMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} (L : LocalGroupAlgebra G) [Group H]

/-- Finite target powers in the inner model neighbourhood lift to genuine
all-bracketings source powers. The proof constructs each domain, using only
binary products in A and the model's small inverse image property. -/
theorem powerIn_of_model_powers (A : Set G) (hA : L.one ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L (ofGroup H)) (W : Set H)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A)
    {u : G} (hu : u ∈ A) (M : ℕ)
    (hp : ∀ n ≤ M, (π.toFun u)^n ∈ W) :
    ∀ n ≤ M, L.PowerIn A u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n = 0
    · subst n
      exact ⟨L.one,hA,Product.nil⟩
    · have hprev : ∀ j ≤ n-1, L.PowerIn A u j := fun j hj => ih j (by omega) (by omega)
      let p := L.powerSegmentOfPowerIn hprev
      have hpmem : ∀ j ≤ n-1, p.power j ∈ A := fun j hj => L.powerSegmentOfPowerIn_mem hprev hj
      obtain ⟨z,hz⟩ := p.extend_product L hpmem hu hdom
      rw [show n-1+1=n by omega] at hz
      have hzmap : π.toFun z = (π.toFun u)^n := by
        have hh := (ofGroup_product_iff H _ _).1 (hz.map π)
        simpa only [List.map_replicate,List.prod_replicate] using hh
      exact ⟨z,hsmall z (hzmap.symm ▸ hp n hn),hz⟩
end LocalGroupAlgebra
end DirectedCycles
