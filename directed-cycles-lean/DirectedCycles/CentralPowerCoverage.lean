import DirectedCycles.CentralCommutators

set_option autoImplicit false
open scoped commutatorElement Classical
namespace DirectedCycles

/-- Bilinearity of central commutators for natural powers. -/
theorem central_commutator_pow_pow {G : Type*} [Group G] (H : Subgroup G)
    (hcentral : ⁅H,(⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (x : H) (y : G) (a b : ℕ) : ⁅x.val^a,y^b⁆ = ⁅x.val,y⁆^(a*b) := by
  have hl := congrArg Subtype.val (map_pow (centralCommutatorLeftHom H hcentral (y^b)) x a)
  have hr := congrArg Subtype.val (map_pow (centralCommutatorRightHom H hcentral x) y b)
  change ⁅x.val^a,y^b⁆ = ⁅x.val,y^b⁆^a at hl
  change ⁅x.val,y^b⁆ = ⁅x.val,y⁆^b at hr
  rw [hr,← pow_mul,Nat.mul_comm] at hl
  exact hl

/-- Power approximations in a subgroup, modulo central errors in the first
entry and derived errors in the second, put commutator powers in that subgroup.
No normality of C is used. -/
theorem central_commutator_power_mem {G : Type*} [Group G] (H C : Subgroup G)
    (hcentral : ⁅H,(⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (a b : ℕ)
    (ha : ∀ x : H, ∃ c : H, c.val ∈ C ∧ ∃ z : Subgroup.center G, x.val^a = c.val*z.val)
    (hb : ∀ y : G, ∃ d ∈ C, ∃ w ∈ commutator G, y^b = d*w)
    (x : H) (y : G) : ⁅x.val,y⁆^(a*b) ∈ C := by
  obtain ⟨c,hc,z,hx⟩ := ha x
  obtain ⟨d,hd,w,hw,hy⟩ := hb y
  have hz : ⁅z.val,y^b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp z.property _).symm
  have hw' : ⁅c.val,w⁆ = 1 := by
    have h := Abelianization.commutator_subset_ker (centralCommutatorRightHom H hcentral c) hw
    exact congrArg Subtype.val h
  rw [← central_commutator_pow_pow H hcentral x y a b,hx,
    commutatorElement_mul_left_eq_conj_mul,hz,mul_one,mul_inv_cancel,one_mul,hy,
    commutatorElement_mul_right_eq_mul_conj,hw',mul_one,mul_inv_cancel_right]
  exact C.mul_mem (C.mul_mem (C.mul_mem hc hd) (C.inv_mem hc)) (C.inv_mem hd)

/-- The same containment holds on the entire central commutator subgroup,
not just on its commutator generators. -/
theorem central_commutator_subgroup_power_mem {G : Type*} [Group G] (H C : Subgroup G)
    (hcentral : ⁅H,(⊤ : Subgroup G)⁆ ≤ Subgroup.center G) (a b : ℕ)
    (ha : ∀ x : H, ∃ c : H, c.val ∈ C ∧ ∃ z : Subgroup.center G, x.val^a = c.val*z.val)
    (hb : ∀ y : G, ∃ d ∈ C, ∃ w ∈ commutator G, y^b = d*w) :
    ∀ x ∈ ⁅H,(⊤ : Subgroup G)⁆, x^(a*b) ∈ C := by
  let K := ⁅H,(⊤ : Subgroup G)⁆
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral x.property) y.val).symm) }
  let q := QuotientGroup.mk' (C.subgroupOf K)
  let S : Set G := {g | ∃ x ∈ H, ∃ y : G, ⁅x,y⁆ = g}
  have hK : K = Subgroup.closure S := by
    simp only [K,Subgroup.commutator_def,Subgroup.mem_top,true_and,S]
  have hgen : Subgroup.closure (K.subtype ⁻¹' S) = ⊤ := by
    subst K
    rw [hK]
    exact Subgroup.closure_preimage_eq_top S
  have hp : ∀ x ∈ K.subtype ⁻¹' S, q x ^ (a*b) = 1 := by
    intro x hx
    obtain ⟨y,hy,z,he⟩ := hx
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change x.val^(a*b) ∈ C
    change ⁅y,z⁆ = x.val at he
    rw [← he]
    exact central_commutator_power_mem H C hcentral a b ha hb ⟨y,hy⟩ z
  intro x hx
  have h := commutative_image_exponent_of_generators q (K.subtype ⁻¹' S) hgen (a*b) hp ⟨x,hx⟩
  rw [← map_pow] at h
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf K) ((⟨x,hx⟩ : K)^(a*b))).mp h

end DirectedCycles
