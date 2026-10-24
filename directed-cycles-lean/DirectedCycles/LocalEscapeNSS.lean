import DirectedCycles.LocalGlobalSubgroup
import DirectedCycles.LocalEscapeNorm

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem escapeNorm_eq_zero_iff_powerSequence {A : Set G} (hA : L.one ∈ A) (g : G) :
    L.escapeNorm A g = 0 ↔ ∃ p : L.PowerSequence g, ∀ n, p.power n ∈ A := by
  classical
  rw [L.escapeNorm_eq_zero_iff hA g]
  constructor
  · intro h
    let p : L.PowerSequence g := {
      power := fun n => Classical.choose (h n)
      product := fun n => (Classical.choose_spec (h n)).2 }
    exact ⟨p,fun n => (Classical.choose_spec (h n)).1⟩
  · rintro ⟨p,hp⟩ n
    exact ⟨p.power n,hp n,p.product n⟩

/-- Exact zero escape in a finite cancellative local group is equivalent to
membership in a genuine cyclic global subgroup. In particular, NSS is exactly
the assertion that zero escape forces the identity. -/
theorem finite_nss_iff_escapeNorm [Finite G] (hL : L.Cancellative)
    {A : Set G} (hA : L.one ∈ A) :
    L.IsNSS A ↔ ∀ g : G, L.escapeNorm A g = 0 → g = L.one := by
  rw [L.finite_nss_iff_powerSequence hL A]
  constructor
  · intro h g hg
    obtain ⟨p,hp⟩ := (L.escapeNorm_eq_zero_iff_powerSequence hA g).1 hg
    exact h g p hp
  · intro h g p hp
    exact h g ((L.escapeNorm_eq_zero_iff_powerSequence hA g).2 ⟨p,hp⟩)
end LocalGroupAlgebra
end DirectedCycles
