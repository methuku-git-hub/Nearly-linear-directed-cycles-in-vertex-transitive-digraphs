import DirectedCycles.SubgroupNSSBasics

set_option autoImplicit false
namespace DirectedCycles
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous injective homomorphism into an NSS group transfers NSS
to its source; no ambient manifold or closed-subgroup theorem is required. -/
theorem nss_of_continuous_injective_hom (f : G →* H) (hf : Continuous f)
    (hinj : Function.Injective f) (hH : HasNoSmallSubgroups H) : HasNoSmallSubgroups G := by
  obtain ⟨V,hV,hV1,hfree⟩ := hH
  refine ⟨f ⁻¹' V,hV.preimage hf,by simpa only [Set.mem_preimage,map_one] using hV1,?_⟩
  intro P hP
  have hmap : (P.map f : Set H) ⊆ V := by
    rintro y ⟨x,hx,rfl⟩
    exact hP hx
  have he := hfree (P.map f) hmap
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply hinj
  rw [map_one]
  have hm : f x ∈ P.map f := Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  rw [he] at hm
  exact Subgroup.mem_bot.mp hm

/-- The quotient by the kernel of a continuous homomorphism into an NSS
group is NSS, using its actual continuous injective kernel lift. -/
theorem kernel_quotient_nss (f : G →* H) (hf : Continuous f)
    (hH : HasNoSmallSubgroups H) : HasNoSmallSubgroups (G ⧸ f.ker) := by
  apply nss_of_continuous_injective_hom (QuotientGroup.kerLift f) _
    (QuotientGroup.kerLift_injective f) hH
  apply continuous_quot_lift
  exact hf

/-- Finite products of NSS groups are NSS with one simultaneous identity
neighbourhood. Infinite products are deliberately not asserted. -/
theorem finite_product_nss {J : Type*} [Finite J] (H : J → Type*) [∀ j, Group (H j)]
    [∀ j, TopologicalSpace (H j)] (hH : ∀ j, HasNoSmallSubgroups (H j)) :
    HasNoSmallSubgroups (∀ j, H j) := by
  classical
  choose V hV hV1 hfree using hH
  let W : Set (∀ j, H j) := ⋂ j, (fun x : ∀ j, H j => x j) ⁻¹' V j
  have hWo : IsOpen W := isOpen_iInter_of_finite (fun j => (hV j).preimage (continuous_apply j))
  have hW1 : (1 : ∀ j, H j) ∈ W := Set.mem_iInter.mpr hV1
  refine ⟨W,hWo,hW1,?_⟩
  intro P hP
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  funext j
  let f : (∀ j, H j) →* H j := Pi.evalMonoidHom H j
  have hm : (P.map f : Set (H j)) ⊆ V j := by
    rintro y ⟨a,ha,rfl⟩
    exact Set.mem_iInter.mp (hP ha) j
  have he := hfree j (P.map f) hm
  have hx' : f x ∈ P.map f := Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  rw [he] at hx'
  exact Subgroup.mem_bot.mp hx'
end DirectedCycles
