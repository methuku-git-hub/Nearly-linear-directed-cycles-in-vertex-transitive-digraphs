import DirectedCycles.BaselineClosureCongruence

set_option autoImplicit false
namespace DirectedCycles

/-- Distinct images after killing a separate all cyclic-coordinate fibres. -/
theorem power_coset_coordinates {I Q R : Type*} [Group Q] [Group R]
    (a : Q) (p : Q →* R) (ha : p a = 1) (r : I → Q)
    (hr : Function.Injective (fun i => p (r i)))
    {i j : I} {u v : ℤ} (he : r i*a^u = r j*a^v) :
    i = j ∧ u ≡ v [ZMOD orderOf a] := by
  have hi : i = j := by
    apply hr
    have h := congrArg p he
    simpa only [map_mul,map_zpow,ha,one_zpow,mul_one] using h
  subst j
  exact ⟨rfl,zpow_eq_zpow_iff_modEq.mp (mul_left_cancel he)⟩

/-- Representatives in one full cyclic interval have unique coordinates. -/
theorem power_coset_coordinates_injective {I Q R : Type*} [Group Q] [Group R]
    (a : Q) (p : Q →* R) (ha : p a = 1) (r : I → Q)
    (hr : Function.Injective (fun i => p (r i))) :
    Function.Injective (fun z : I × Fin (orderOf a) => r z.1*a^z.2.val) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ he
  have hi : i = j := by
    apply hr
    have h := congrArg p he
    simpa only [map_mul,map_pow,ha,one_pow,mul_one] using h
  subst j
  have huv : u = v := Fin.ext (pow_injOn_Iio_orderOf u.isLt v.isLt (mul_left_cancel he))
  subst v
  rfl

/-- Modulo B, the normalized coordinates of the chosen quotient positions
are distinct throughout a full interval of length |K/B|. -/
theorem element_power_coordinates_injective {G I : Type*} [Group G] [Finite G]
    (a : G) (r : I → G)
    (hr : Function.Injective (fun i => QuotientGroup.mk' (elementClosure a) (r i))) :
    Function.Injective (fun z : I × Fin (orderOf (QuotientGroup.mk' (elementCommutators a) a)) =>
      QuotientGroup.mk' (elementCommutators a) (r z.1) *
        (QuotientGroup.mk' (elementCommutators a) a)^z.2.val) := by
  let p := QuotientGroup.map (elementCommutators a) (elementClosure a) (MonoidHom.id G)
    (by simpa only [Subgroup.comap_id] using (show elementCommutators a ≤ elementClosure a from le_sup_right))
  refine power_coset_coordinates_injective (QuotientGroup.mk' (elementCommutators a) a) p ?_
    (fun i => QuotientGroup.mk' (elementCommutators a) (r i)) hr
  change QuotientGroup.mk' (elementClosure a) a = 1
  exact (QuotientGroup.eq_one_iff a).mpr (mem_elementClosure a)

end DirectedCycles
