import DirectedCycles.SubgroupNSSBasics
import Mathlib.Algebra.Group.Subgroup.Map

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- A subgroup trapped in a compact containing subgroup is trapped in the
specified kernel whenever its actual image lies in a subgroup-free quotient
window. This uses the image subgroup, rather than individual power bounds. -/
theorem trapped_subgroups_in_kernel (H : Subgroup G) (N : Subgroup H)
    [N.Normal] (V R : Set G)
    (htrap : ∀ P : Subgroup G, (P : Set G) ⊆ V → P ≤ H)
    (hRV : R ⊆ V)
    (B : Set (H ⧸ N)) (hB : SubgroupFreeSet B)
    (hRB : ∀ x : H, x.val ∈ R → QuotientGroup.mk' N x ∈ B) :
    ∀ P : Subgroup G, (P : Set G) ⊆ R → P ≤ N.map H.subtype := by
  let q := QuotientGroup.mk' N
  intro P hP
  have hPH : P ≤ H := htrap P (hP.trans hRV)
  have himage : ((P.subgroupOf H).map q : Set (H ⧸ N)) ⊆ B := by
    rintro y ⟨x,hx,rfl⟩
    exact hRB x (hP hx)
  have htrivial := hB ((P.subgroupOf H).map q) himage
  intro x hx
  let xH : H := ⟨x,hPH hx⟩
  have hq : q xH ∈ (P.subgroupOf H).map q := Subgroup.mem_map.mpr ⟨xH,hx,rfl⟩
  rw [htrivial] at hq
  have hk : xH ∈ N := (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.mp hq)
  exact Subgroup.mem_map.mpr ⟨xH,hk,rfl⟩
end DirectedCycles
