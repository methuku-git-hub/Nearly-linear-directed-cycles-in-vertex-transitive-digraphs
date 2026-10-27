module

public import DirectedCycles.NSSTargetMaps
public import DirectedCycles.NSSSubquotientFromTrapping

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G J : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (H : J → Type*) [∀ j, Group (H j)] [∀ j, TopologicalSpace (H j)] [∀ j, T1Space (H j)]

/-- Continuous homomorphisms into NSS targets that separate the identity
give arbitrarily small compact normal kernels with actual NSS quotients.
Compactness selects finitely many maps before taking their common kernel. -/
theorem compact_nss_approximation_of_separating_homs
    (f : ∀ j, G →* H j) (hf : ∀ j, Continuous (f j)) (hNSS : ∀ j, HasNoSmallSubgroups (H j))
    (hsep : ∀ x : G, x ≠ 1 → ∃ j, f j x ≠ 1) : HasCompactNSSApproximation G := by
  classical
  intro U hU hU1
  let O : J → Set G := fun j => (f j ⁻¹' {1})ᶜ
  have hOo : ∀ j, IsOpen (O j) := fun j => (isClosed_singleton.preimage (hf j)).isOpen_compl
  have hcover : Uᶜ ⊆ ⋃ j, O j := by
    intro x hx
    have hx1 : x ≠ 1 := fun he => hx (he.symm ▸ hU1)
    obtain ⟨j,hj⟩ := hsep x hx1
    exact Set.mem_iUnion.mpr ⟨j,hj⟩
  obtain ⟨F,hF⟩ := hU.isClosed_compl.isCompact.elim_finite_subcover O hOo hcover
  let p : G →* (∀ j : ↥F, H j.val) := MonoidHom.pi (fun j : ↥F => f j.val)
  have hp : Continuous p := continuous_pi (fun j : ↥F => hf j.val)
  have hpc : IsCompact (p.ker : Set G) := (isClosed_singleton.preimage hp).isCompact
  have hpU : (p.ker : Set G) ⊆ U := by
    intro x hx
    by_contra hn
    obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp (hF hn)
    have he : p x = 1 := hx
    have he' := congrArg (fun z : ∀ j : ↥F, H j.val => z ⟨j,hj⟩) he
    exact hxj he'
  exact ⟨p.ker,inferInstance,hpc,hpU,
    kernel_quotient_nss p hp (finite_product_nss (fun j : ↥F => H j.val) (fun j => hNSS j.val))⟩
end DirectedCycles
