module

public import DirectedCycles.CyclicLayerWords

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Generation by full-round products gives strong connectivity of the actual
cyclic-layer digraph. No symmetry between different layers is assumed. -/
theorem cyclicLayer_stronglyConnected {G : Type*} [Group G] [Finite G]
    {T : ℕ} [NeZero T] (S : ZMod T → Set G) (hne : ∀ i, (S i).Nonempty)
    (hgen : Subgroup.closure (layerRoundProducts S) = ⊤) :
    StronglyConnected (CyclicLayerDigraph S) := by
  classical
  choose beta hbeta using hne
  have hbase : ∀ x y : G, Reachable (CyclicLayerDigraph S) (x,0) (y,0) := by
    intro x y
    have h := cyclicLayer_reachable_translate S x (cyclicLayer_base_reachable S hgen (x⁻¹*y))
    simpa only [mul_one,mul_inv_cancel_left] using h
  have hfrom : ∀ x y : G, ∀ i : ZMod T, Reachable (CyclicLayerDigraph S) (x,0) (y,i) := by
    intro x y i
    let xs := baselineLayerWord beta 0 i.val
    have h := layerWord_reachable S (y*xs.prod⁻¹) 0 xs (baselineLayerWord_allowed S beta hbeta 0 i.val)
    have ht : (xs.length : ZMod T) = i := by
      rw [baselineLayerWord_length,ZMod.natCast_zmod_val]
    rw [ht,zero_add,inv_mul_cancel_right] at h
    exact (hbase x (y*xs.prod⁻¹)).trans h
  intro u v
  let xs := baselineLayerWord beta u.2 (T-u.2.val)
  have h := layerWord_reachable S u.1 u.2 xs
    (baselineLayerWord_allowed S beta hbeta u.2 (T-u.2.val))
  have ht : u.2 + (xs.length : ZMod T) = 0 := by
    rw [baselineLayerWord_length,Nat.cast_sub (ZMod.val_lt u.2).le,
      ZMod.natCast_self,ZMod.natCast_zmod_val]
    abel
  rw [ht] at h
  exact h.trans (hfrom (u.1*xs.prod) v.1 v.2)

end DirectedCycles
