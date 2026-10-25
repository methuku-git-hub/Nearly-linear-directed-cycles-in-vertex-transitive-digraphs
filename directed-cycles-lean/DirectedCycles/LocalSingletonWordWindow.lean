module

public import DirectedCycles.LocalApproximateGroups
public import DirectedCycles.LocalPowerGrid
public import DirectedCycles.LocalZeroEscapeSubgroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem allProductsDefined_singleton_one (N : ℕ) : L.AllProductsDefined {L.one} N := by
  intro l _ hl
  have he : l = List.replicate l.length L.one := List.eq_replicate_of_mem fun x hx => hl x hx
  exact ⟨L.one,he ▸ L.product_replicate_one l.length⟩

theorem wordPower_singleton_one (N : ℕ) : L.wordPower {L.one} N = {L.one} := by
  ext x
  constructor
  · rintro ⟨l,hlen,hl,hp⟩
    have he : l = List.replicate N L.one := List.eq_replicate_iff.2 ⟨hlen,fun x hx => hl x hx⟩
    exact hp.unique L (he ▸ L.product_replicate_one N)
  · intro hx
    exact ⟨List.replicate N L.one,List.length_replicate,fun _ h => (List.mem_replicate.mp h).2,
      hx.symm ▸ L.product_replicate_one N⟩
end LocalGroupAlgebra

/-- The identity singleton supplies a genuine approximate group on indices
outside an ultrafilter-large set, without changing any internal source set. -/
theorem local_singleton_one_approximate {G : Type*} (L : LocalGroupAlgebra G) {K : ℕ} (hK : 1 ≤ K) :
    IsLocalFiniteApproximateGroup L K {L.one} := by
  classical
  have hi : ∀ x ∈ ({L.one} : Finset G), L.inv x ∈ ({L.one} : Finset G) := by
    intro x hx
    have he := Finset.mem_singleton.mp hx
    simp only [he,L.inv_one,Finset.mem_singleton]
  refine ⟨hK,Finset.mem_singleton_self _,hi,?_,⟨{L.one},by simpa using hK,hi,?_,?_⟩⟩
  · simpa only [Finset.coe_singleton] using L.allProductsDefined_singleton_one 200
  · simp only [Finset.coe_singleton,L.wordPower_singleton_one,Set.Subset.refl]
  · simp only [Finset.coe_singleton,L.wordPower_singleton_one]
    intro x hx
    exact ⟨L.one,rfl,L.one,rfl,hx.symm ▸ L.one_mul L.one⟩
end DirectedCycles
