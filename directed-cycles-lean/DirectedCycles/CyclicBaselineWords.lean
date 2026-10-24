import DirectedCycles.CoordinateNormalization

set_option autoImplicit false
namespace DirectedCycles

/-- One fixed run followed by the baseline connector. -/
def runConnectorBlock {G : Type*} [Group G] (a : G) (D l : ℕ) (s : G) : List G :=
  List.replicate l a ++ [a^D*s]

@[simp] theorem runConnectorBlock_length {G : Type*} [Group G] (a : G) (D l : ℕ) (s : G) :
    (runConnectorBlock a D l s).length = l+1 := by simp [runConnectorBlock]

theorem runConnectorBlock_prod {G : Type*} [Group G] (a : G) (D l : ℕ) (s : G) :
    (runConnectorBlock a D l s).prod = a^(l+D)*s := by
  simp only [runConnectorBlock,List.prod_append,List.prod_replicate,List.prod_singleton,pow_add,mul_assoc]

/-- The list of retained-position baseline labels. -/
def cyclicBaselineWord {G : Type*} [Group G] (a : G) (D : ℕ) (data : List (ℕ × G)) : List G :=
  data.flatMap (fun z => runConnectorBlock a D z.1 z.2)

@[simp] theorem cyclicBaselineWord_length {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) :
    (cyclicBaselineWord a D data).length = (data.map (fun z => z.1+1)).sum := by
  induction data with
  | nil => rfl
  | cons z data ih =>
    change (runConnectorBlock a D z.1 z.2 ++ cyclicBaselineWord a D data).length = _
    rw [List.length_append,runConnectorBlock_length,ih]
    rfl

/-- Modulo B, inserted powers commute past all original cycle labels. -/
theorem cyclicBaselineWord_quotient {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) :
    QuotientGroup.mk' (elementCommutators a) (cyclicBaselineWord a D data).prod =
      (QuotientGroup.mk' (elementCommutators a) a)^((data.map (fun z => z.1+D)).sum) *
        QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod := by
  let q := QuotientGroup.mk' (elementCommutators a)
  induction data with
  | nil => simp [cyclicBaselineWord]
  | cons z data ih =>
    change q ((runConnectorBlock a D z.1 z.2 ++ cyclicBaselineWord a D data).prod) = _
    rw [List.prod_append,map_mul,runConnectorBlock_prod,map_mul,map_pow,ih]
    have hc : Commute (q a) (q z.2) :=
      (Subgroup.mem_center_iff.mp (element_mod_commutators_central a) (q z.2)).symm
    simp only [List.map_cons,List.sum_cons,List.prod_cons,map_mul]
    rw [mul_assoc,← mul_assoc (q z.2),
      (hc.pow_left ((data.map (fun z => z.1+D)).sum)).eq.symm]
    simp only [pow_add,mul_assoc]
    rfl

/-- The closure congruence on the baseline is the exact condition needed for
its product to lie in B. -/
theorem cyclicBaselineWord_mem {G : Type*} [Group G]
    (a : G) (D : ℕ) (data : List (ℕ × G))
    (hclose : (QuotientGroup.mk' (elementCommutators a) a)^((data.map (fun z => z.1+D)).sum) *
        QuotientGroup.mk' (elementCommutators a) (data.map Prod.snd).prod = 1) :
    (cyclicBaselineWord a D data).prod ∈ elementCommutators a := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (elementCommutators a) (cyclicBaselineWord a D data).prod = 1
  rw [cyclicBaselineWord_quotient,hclose]

end DirectedCycles
