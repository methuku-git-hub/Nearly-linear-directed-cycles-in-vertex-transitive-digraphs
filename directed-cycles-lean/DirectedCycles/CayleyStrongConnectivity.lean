import DirectedCycles.CayleyWords

set_option autoImplicit false
namespace DirectedCycles

theorem cayley_reachable_translate {G : Type*} [Group G] (S : Set G) (g : G)
    {x y : G} (h : Reachable (CayleyDigraph S) x y) :
    Reachable (CayleyDigraph S) (g*x) (g*y) :=
  reachable_map (fun z => g*z) (by
    intro u v huv
    obtain ⟨s,hs,he⟩ := huv
    exact ⟨s,hs,by rw [he,mul_assoc]⟩) h

theorem finite_cayley_stronglyConnected {G : Type*} [Group G] [Finite G]
    (S : Set G) (hgen : Subgroup.closure S = ⊤) : StronglyConnected (CayleyDigraph S) := by
  let R : Submonoid G := {
    carrier := {g | Reachable (CayleyDigraph S) 1 g}
    one_mem' := Relation.ReflTransGen.refl
    mul_mem' := by
      intro x y hx hy
      have hh := cayley_reachable_translate S x hy
      rw [mul_one] at hh
      exact hx.trans hh
  }
  have hR : Submonoid.closure S ≤ R := by
    apply Submonoid.closure_le.mpr
    intro s hs
    exact Relation.ReflTransGen.single ⟨s,hs,(one_mul s).symm⟩
  have htop : Submonoid.closure S = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite,hgen,Subgroup.top_toSubmonoid]
  intro x y
  have hbase : Reachable (CayleyDigraph S) 1 (x⁻¹*y) := hR (by rw [htop]; trivial)
  simpa only [mul_one,mul_inv_cancel_left] using cayley_reachable_translate S x hbase

end DirectedCycles
