import DirectedCycles.LocalSubgroupTransport
import DirectedCycles.LocalEscapeMaps

set_option autoImplicit false
namespace DirectedCycles

/-- A cyclic NSS bound in the actual ambient group excludes every global
subgroup of its restricted local window. -/
theorem global_window_nss {G : Type*} [Group G] (W : Set G) (h1 : (1 : G) ∈ W)
    (hi : ∀ x ∈ W, x⁻¹ ∈ W)
    (hNSS : ∀ x : G, (∀ n : ℕ, x^n ∈ W) → x = 1) :
    ((LocalGroupAlgebra.ofGroup G).restrict W h1 hi).IsNSS Set.univ := by
  let L := (LocalGroupAlgebra.ofGroup G).restrict W h1 hi
  let f := LocalGroupHom.inclusion (LocalGroupAlgebra.ofGroup G) W h1 hi
  intro S hS _ x hx
  have hg := hS.image f
  have hx1 : x.val = 1 := by
    apply hNSS x.val
    intro n
    have hp := (LocalGroupAlgebra.ofGroup_powerIn_iff (f.toFun '' S) x.val n).1
      (hg.powerIn (show x.val ∈ f.toFun '' S from ⟨x,hx,rfl⟩) n)
    obtain ⟨y,_hy,he⟩ := hp
    exact he ▸ y.property
  change x = L.one
  exact Subtype.ext hx1
end DirectedCycles
