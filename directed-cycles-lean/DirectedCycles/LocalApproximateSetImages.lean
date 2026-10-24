import DirectedCycles.LocalApproximateSets
import DirectedCycles.LocalWordPowerMaps

set_option autoImplicit false
namespace DirectedCycles
namespace IsLocalApproximateSet
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    {K : ℕ} {A : Set G}

/-- Actual local homomorphisms preserve approximate sets, including the
200-letter domain and the finite symmetric cover inside the third power. -/
theorem image (hA : IsLocalApproximateSet L K A) (f : LocalGroupHom L M) :
    IsLocalApproximateSet M K (f.toFun '' A) := by
  classical
  refine ⟨hA.one_le,⟨L.one,hA.one_mem,f.map_one⟩,?_,hA.allProducts.image f,?_⟩
  · rintro x ⟨a,ha,rfl⟩
    exact ⟨L.inv a,hA.inv_mem a ha,f.map_inv a⟩
  · obtain ⟨X,hXcard,hXi,hX3,hcover⟩ := hA.cover
    refine ⟨X.image f.toFun,Finset.card_image_le.trans hXcard,?_,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨L.inv a,hXi a ha,f.map_inv a⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact LocalGroupAlgebra.wordPower_image_subset f A 3 ⟨a,hX3 ha,rfl⟩
    · rw [← LocalGroupAlgebra.wordPower_image f hA.allProducts (by omega : 2 ≤ 200)]
      rintro x ⟨z,hz,rfl⟩
      obtain ⟨a,ha,b,hb,hm⟩ := hcover hz
      exact ⟨f.toFun a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,f.toFun b,⟨b,hb,rfl⟩,f.map_mul hm⟩
end IsLocalApproximateSet
end DirectedCycles
