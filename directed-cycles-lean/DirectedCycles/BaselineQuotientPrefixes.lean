import DirectedCycles.CyclicBaselineWords

set_option autoImplicit false
namespace DirectedCycles

/-- Inserted powers disappear modulo K, preserving the quotient-cycle prefixes. -/
theorem cyclicBaselineWord_mod_elementClosure {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) :
    QuotientGroup.mk' (elementClosure a) (cyclicBaselineWord a D data).prod =
      QuotientGroup.mk' (elementClosure a) (data.map Prod.snd).prod := by
  let q := QuotientGroup.mk' (elementClosure a)
  have ha : q a = 1 := (QuotientGroup.eq_one_iff a).mpr (mem_elementClosure a)
  induction data with
  | nil => rfl
  | cons z data ih =>
    change q ((runConnectorBlock a D z.1 z.2 ++ cyclicBaselineWord a D data).prod) = _
    rw [List.prod_append,map_mul,runConnectorBlock_prod,map_mul,map_pow,ha,one_pow,one_mul,ih]
    simp only [List.map_cons,List.prod_cons,map_mul]
    rfl

/-- Equality in a normal quotient gives the required left-coset factorization. -/
theorem quotient_prefix_left_factor {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (p g : G) (h : QuotientGroup.mk' N p = QuotientGroup.mk' N g) :
    ∃ k ∈ N, p = k*g := by
  refine ⟨p*g⁻¹,?_,by simp⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (p*g⁻¹) = 1
  rw [map_mul,map_inv,h,mul_inv_cancel]

/-- Each connector's prefix lies in K times the corresponding quotient prefix. -/
theorem cyclicBaseline_connector_prefix {G : Type*} [Group G]
    (a : G) (D l : ℕ) (data : List (ℕ × G)) :
    ∃ k ∈ elementClosure a,
      (cyclicBaselineWord a D data).prod*a^l = k*(data.map Prod.snd).prod := by
  apply quotient_prefix_left_factor (elementClosure a)
  rw [map_mul,map_pow,cyclicBaselineWord_mod_elementClosure]
  have ha : QuotientGroup.mk' (elementClosure a) a = 1 :=
    (QuotientGroup.eq_one_iff a).mpr (mem_elementClosure a)
  rw [ha,one_pow,mul_one]

end DirectedCycles
