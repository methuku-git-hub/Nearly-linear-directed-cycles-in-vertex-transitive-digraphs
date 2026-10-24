import DirectedCycles.CyclicResiduePowers
import DirectedCycles.RunPrefixResidues
import DirectedCycles.CycleRunData
import DirectedCycles.RetainedPositions

set_option autoImplicit false
namespace DirectedCycles

theorem cycleRunData_prefix_sum {G : Type*} {ell : ℕ}
    (l : Fin ell → ℕ) (s : Fin ell → G) (D : ℕ) (i : Fin ell) :
    (((cycleRunData l s).take i.val).map (fun z => z.1+D)).sum = runPrefixSum l D i.castSucc := by
  simp only [cycleRunData,List.map_take,List.map_ofFn,Function.comp_def,runPrefixSum,Fin.val_castSucc]

/-- The actual connector source coordinates are exactly the chosen
residue intervals, after accounting for all preceding runs. -/
theorem actual_run_source_residue {G : Type*} [Group G] [Finite G] {ell : ℕ}
    (a : G) (D : ℕ) (l : Fin ell → ℕ) (s : Fin ell → G)
    (v : Fin ell → ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a)))
    (hv : ∀ i, (runPrefixSum l D i.castSucc : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a)))+
      (l i : ZMod (orderOf (QuotientGroup.mk' (elementCommutators a) a))) = v i)
    (i : Fin ell) (u : ℕ) :
    QuotientGroup.mk' (elementCommutators a)
      (runReference a D (cycleRunData l s) ⟨i.val,by rw [cycleRunData_length]; exact i.isLt⟩) *
        (QuotientGroup.mk' (elementCommutators a) a)^(l i+u) =
      residuePower (QuotientGroup.mk' (elementCommutators a) a) (v i+u) *
        QuotientGroup.mk' (elementCommutators a) ((List.ofFn s).take i.val).prod := by
  let q := QuotientGroup.mk' (elementCommutators a)
  let b := q a
  let g := ((List.ofFn s).take i.val).prod
  have href : q (runReference a D (cycleRunData l s) ⟨i.val,by rw [cycleRunData_length]; exact i.isLt⟩) =
      b^(runPrefixSum l D i.castSucc)*q g := by
    rw [runReference,cyclicBaselineWord_quotient]
    change b^(((cycleRunData l s).take i.val).map (fun z => z.1+D)).sum *
      q (((cycleRunData l s).take i.val).map Prod.snd).prod =
      b^(runPrefixSum l D i.castSucc)*q g
    rw [cycleRunData_prefix_sum,List.map_take,cycleRunData_snd]
  have hc : Commute b (q g) := (Subgroup.mem_center_iff.mp (element_mod_commutators_central a) (q g)).symm
  change q (runReference a D (cycleRunData l s) ⟨i.val,by rw [cycleRunData_length]; exact i.isLt⟩)*b^(l i+u) =
    residuePower b (v i+u)*q g
  rw [href,mul_assoc,← (hc.pow_left (l i+u)).eq,← mul_assoc,← pow_add]
  rw [← residuePower_natCast b (runPrefixSum l D i.castSucc+(l i+u))]
  congr 2
  push_cast
  rw [← add_assoc,hv i]

end DirectedCycles
