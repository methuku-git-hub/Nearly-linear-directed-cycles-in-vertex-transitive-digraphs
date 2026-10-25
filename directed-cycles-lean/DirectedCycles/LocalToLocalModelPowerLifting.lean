module

public import DirectedCycles.LocalPowerExtension
public import DirectedCycles.LocalPowerSegmentMaps

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} (L : LocalGroupAlgebra G) (Q : LocalGroupAlgebra H)

/-- Finite target powers in the inner model neighbourhood lift to genuine
all-bracketings source powers. The proof constructs each domain, using only
binary products in A and the model's small inverse image property. -/
theorem powerIn_of_local_model_segment (A : Set G) (hA : L.one ∈ A)
    (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L Q) (W : Set H)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A)
    {u : G} (hu : u ∈ A) (M : ℕ)
    (q : Q.PowerSegment (π.toFun u) M) (hp : ∀ n ≤ M, q.power n ∈ W) :
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
      have hzmap : π.toFun z = q.power n := by
        have hh : Q.Product (List.replicate n (π.toFun u)) (π.toFun z) := by
          simpa only [List.map_replicate] using hz.map π
        exact hh.unique Q (q.product n hn)
      exact ⟨z,hsmall z (hzmap.symm ▸ hp n hn),hz⟩
end LocalGroupAlgebra
end DirectedCycles
