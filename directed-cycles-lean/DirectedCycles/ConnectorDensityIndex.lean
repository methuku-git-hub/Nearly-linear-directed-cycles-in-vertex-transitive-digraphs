module

public import DirectedCycles.ConnectorSystemIndex
public import DirectedCycles.DenseBounds

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Positive uniform exponent, enlarged by one to cover the trivial B case. -/
def auxiliaryIndexPower (r c n : ℕ) : ℕ :=
  (n+1)*(∑ i ∈ Finset.range (c/2), (i+1)*(∑ j ∈ Finset.range c, r^(j+1))^(i+1)) + 1

def auxiliaryIndexConstant (r c n : ℕ) : ℕ :=
  (denseMultiplierConstant (∑ j ∈ Finset.range c, r^(j+1)) (n+1))^auxiliaryIndexPower r c n

def auxiliaryIndexExponent (r c n : ℕ) : ℕ :=
  denseMultiplierExponent (∑ j ∈ Finset.range c, r^(j+1)) (n+1)*auxiliaryIndexPower r c n

theorem auxiliaryIndexConstant_pos (r c n : ℕ) : 0 < auxiliaryIndexConstant r c n :=
  pow_pos (denseMultiplierConstant_pos _ _) _

theorem auxiliaryIndexExponent_pos (r c n : ℕ) : 0 < auxiliaryIndexExponent r c n :=
  Nat.mul_pos (denseMultiplierExponent_pos _ _) (Nat.zero_lt_succ _)

/-- The density bound for the actual connector system, with explicit constants
independent of G, the cycle and its length. Distinct quotient vertices make the
density exactly ell/|G/K|. -/
theorem connector_system_density_index {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (a : G) (r c n ell : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (hn : c ≤ n) (hell : 0 < ell) (C : Subgroup (elementCommutators a))
    (g : Fin (ell+1) → G) (s p t : Fin ell → G) (h0 : g 0 = 1)
    (hstep : ∀ i : Fin ell, g i.succ = g i.castSucc*s i)
    (hg : Function.Injective (fun i : Fin ell => QuotientGroup.mk' (elementClosure a) (g i.castSucc)))
    (hp : ∀ i, ∃ k ∈ elementClosure a, p i = k*g i.castSucc)
    (mu : Fin ell → Fin (n+1+1) → elementCommutators a)
    (hmu : ∀ i j, (mu i j).val = p i*connectorWord a (s i) (n+1) j.val*(t i)⁻¹)
    (hC : ∀ i j, mu i j ∈ C) :
    (C.index : ℝ) ≤ auxiliaryIndexConstant r c n *
      ((Nat.card (G ⧸ elementClosure a) : ℝ)/ell)^auxiliaryIndexExponent r c n := by
  classical
  let q := QuotientGroup.mk' (elementClosure a)
  let E : Finset (G ⧸ elementClosure a) := Finset.univ.image (fun i : Fin ell => q (g i.castSucc))
  have hE : E.Nonempty := ⟨q (g ⟨0,by omega⟩),Finset.mem_image.mpr
    ⟨⟨0,hell⟩,Finset.mem_univ _,rfl⟩⟩
  have hcard : E.card = ell := by
    rw [Finset.card_image_of_injective _ hg]
    simp
  have hset : (E : Set (G ⧸ elementClosure a)) =
      Set.range (fun i : Fin ell => q (g i.castSucc)) := by
    ext x
    simp [E]
  obtain ⟨m,hm,hbound,hspan⟩ := nilpotent_dense_generation r c (n+1)
    ((Group.rank_le_of_surjective q (QuotientGroup.mk'_surjective _)).trans hr)
    ((Group.nilpotencyClass_quotient_le (elementClosure a)).trans hc) E hE
  rw [hcard] at hbound
  rw [hset] at hspan
  have hi := connector_system_index_of_multiplier a r c n ell hr hc hn C g s p t h0 hstep hp
    mu hmu hC m hm hspan
  have hi' : C.index ≤ m^auxiliaryIndexPower r c n :=
    hi.trans (Nat.pow_le_pow_right hm (Nat.le_succ _))
  have him : (C.index : ℝ) ≤ (m : ℝ)^auxiliaryIndexPower r c n := by exact_mod_cast hi'
  refine him.trans ?_
  calc
    (m : ℝ)^auxiliaryIndexPower r c n ≤
      ((denseMultiplierConstant (∑ j ∈ Finset.range c, r^(j+1)) (n+1) : ℝ) *
      ((Nat.card (G ⧸ elementClosure a) : ℝ)/ell)^denseMultiplierExponent
        (∑ j ∈ Finset.range c, r^(j+1)) (n+1))^auxiliaryIndexPower r c n := by
          gcongr
    _ = _ := by simp only [auxiliaryIndexConstant,auxiliaryIndexExponent,Nat.cast_pow,mul_pow,pow_mul]

end DirectedCycles
