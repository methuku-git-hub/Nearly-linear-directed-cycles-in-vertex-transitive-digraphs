import DirectedCycles.RelativeCommutatorWeights

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- A subgroup becomes central after killing all its ambient commutators. -/
theorem subgroup_image_central_of_commutator_le {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (U : Subgroup G)
    (hU : ⁅U,(⊤ : Subgroup G)⁆ ≤ f.ker) : U.map f ≤ Subgroup.center Q := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  rw [← Subgroup.map_top_of_surjective f hf,← Subgroup.map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr hU

/-- Multiplication in the first input is additive in a quotient in which
all relevant commutator values are central. -/
theorem commutator_mul_left_mod {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (A B : Subgroup G)
    (hc : ∀ z ∈ ⁅A,B⁆, f z ∈ Subgroup.center Q)
    {x y z : G} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ B) :
    f ⁅x*y,z⁆ = f ⁅x,z⁆ * f ⁅y,z⁆ := by
  have hcy := hc _ (Subgroup.commutator_mem_commutator hy hz)
  have hcx := hc _ (Subgroup.commutator_mem_commutator hx hz)
  rw [commutatorElement_mul_left_eq_conj_mul]
  simp only [_root_.map_mul,_root_.map_inv]
  rw [Subgroup.mem_center_iff.mp hcy (f x),mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hcx _)

/-- The corresponding second-input multiplication identity. -/
theorem commutator_mul_right_mod {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (A B : Subgroup G)
    (hc : ∀ z ∈ ⁅A,B⁆, f z ∈ Subgroup.center Q)
    {x y z : G} (hx : x ∈ A) (_hy : y ∈ B) (hz : z ∈ B) :
    f ⁅x,y*z⁆ = f ⁅x,y⁆ * f ⁅x,z⁆ := by
  have hcz := hc _ (Subgroup.commutator_mem_commutator hx hz)
  rw [commutatorElement_mul_right_eq_mul_conj]
  simp only [_root_.map_mul,_root_.map_inv]
  calc
    f ⁅x,y⁆ * f y * f ⁅x,z⁆ * (f y)⁻¹ = f ⁅x,y⁆ * (f y*f ⁅x,z⁆*(f y)⁻¹) := by group
    _ = f ⁅x,y⁆ * f ⁅x,z⁆ := by
      rw [Subgroup.mem_center_iff.mp hcz (f y),mul_inv_cancel_right]

/-- Equality modulo L may be substituted in the first commutator input
if commutators of L with the second input subgroup vanish modulo N. -/
theorem commutator_congr_left_mod {G : Type*} [Group G]
    (L N B : Subgroup G) [L.Normal] [N.Normal] (h : ⁅L,B⁆ ≤ N)
    {x y z : G} (hz : z ∈ B)
    (he : QuotientGroup.mk' L x = QuotientGroup.mk' L y) :
    QuotientGroup.mk' N ⁅x,z⁆ = QuotientGroup.mk' N ⁅y,z⁆ := by
  let q := QuotientGroup.mk' N
  have hk : x⁻¹*y ∈ L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' L (x⁻¹*y) = 1
    rw [_root_.map_mul,_root_.map_inv,he,inv_mul_cancel]
  have hz' : q ⁅x⁻¹*y,z⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (h (Subgroup.commutator_mem_commutator hk hz))
  have hy : y = x*(x⁻¹*y) := by group
  rw [hy,commutatorElement_mul_left_eq_conj_mul]
  change q ⁅x,z⁆ = q (x*⁅x⁻¹*y,z⁆*x⁻¹*⁅x,z⁆)
  rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,_root_.map_inv,hz']
  group

/-- The symmetric congruence for the second commutator input. -/
theorem commutator_congr_right_mod {G : Type*} [Group G]
    (L N A : Subgroup G) [L.Normal] [N.Normal] (h : ⁅A,L⁆ ≤ N)
    {x y z : G} (hx : x ∈ A)
    (he : QuotientGroup.mk' L y = QuotientGroup.mk' L z) :
    QuotientGroup.mk' N ⁅x,y⁆ = QuotientGroup.mk' N ⁅x,z⁆ := by
  have h' : ⁅L,A⁆ ≤ N := by rw [Subgroup.commutator_comm]; exact h
  have hh := commutator_congr_left_mod L N A h' hx he
  have hinv := congrArg Inv.inv hh
  simpa only [← _root_.map_inv,commutatorElement_inv] using hinv

end DirectedCycles
