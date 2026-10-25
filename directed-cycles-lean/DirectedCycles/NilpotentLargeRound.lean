module

public import DirectedCycles.SpanningCycleLift
public import DirectedCycles.DirectedLifting
public import DirectedCycles.DensityPowerArithmetic
public import DirectedCycles.RoundSpanning

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A large cyclic normal factor in a full-round product gives the layer
bound. Under the fixed prime cutoff, the separate linear spanning lift also
supplies all layer spanning invariants. -/
theorem nilpotent_large_round_cycle {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {T : ℕ} [NeZero T] (S : ZMod T → Set G) (xs : List G) (hlen : xs.length = T)
    (hxs : LayerWord S 0 xs) (r c n : ℕ) (hr : Group.rank G ≤ r)
    (hc : Group.nilpotencyClass G ≤ c) (hcn : c ≤ n)
    (hh : 8*(n+1)+4 < Nat.card (elementClosure xs.prod ⧸
      (elementCommutators xs.prod).subgroupOf (elementClosure xs.prod)))
    (hproper : elementClosure xs.prod ≠ ⊤)
    (bq bl eps : ℝ) (hbq : 0 < bq) (hbl : 0 < bl) (heps : 0 ≤ eps)
    (hquot : CayleySpanningBound (G ⧸ elementClosure xs.prod) (n+1) bq
      (eps/(auxiliaryIndexExponent r c n+1)))
    (hlayer : LayerSpanningBound (elementCommutators xs.prod) (n+1) bl eps)
    (hsub : ∀ U : Subgroup (elementCommutators xs.prod), LayerCycleLowerBound U bl eps)
    (hsc : StronglyConnected (CyclicLayerDigraph S)) :
    let k := auxiliaryIndexExponent r c n+1
    let b := min (bl/(4*(auxiliaryIndexConstant r c n : ℝ))*bq^k) (bl/4*bq)
    ∃ L : Cycle (CyclicLayerDigraph S), b*T*(Nat.card G : ℝ)^(1-eps) ≤ L.length ∧
      (AbovePrimeCutoff G (n+1) → ∀ z, SpansTruncation (n+1) (L.layerCoordinates z)) := by
  let a := xs.prod
  let K := elementClosure a
  let B := elementCommutators a
  let q := QuotientGroup.mk' K
  let A := singleRoundProducts S xs
  let k := auxiliaryIndexExponent r c n+1
  let beta := eps/(k : ℝ)
  let d := bl/(4*(auxiliaryIndexConstant r c n : ℝ))
  let b := min (d*bq^k) (bl/4*bq)
  let : Nontrivial (G ⧸ K) := QuotientGroup.nontrivial_iff.mpr hproper
  have hA : Subgroup.closure A = ⊤ := by
    rw [singleRoundProducts_generate S xs hlen hxs,cyclicLayer_rounds_generate S hsc]
  have hqA : Subgroup.closure (q '' A) = ⊤ := by
    rw [← MonoidHom.map_closure,hA,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  obtain ⟨Q,hQ,hQspan⟩ := hquot inferInstance (q '' A) hqA
  have ha : a ∈ A := ⟨xs,Or.inl rfl,hxs,rfl⟩
  have hqpos : (0 : ℝ) < Nat.card (G ⧸ K) := by exact_mod_cast (Nat.card_pos (α := G ⧸ K))
  have hq1 : (1 : ℝ) ≤ Nat.card (G ⧸ K) := by exact_mod_cast (Nat.card_pos (α := G ⧸ K))
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  have hG1 : (1 : ℝ) ≤ Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  have hKpos : (0 : ℝ) < Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hk1 : (1 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast (Nat.le_add_left 1 (auxiliaryIndexExponent r c n))
  have hbetaeps : beta ≤ eps := div_le_self heps hk1
  have heq : (k : ℝ)*beta = eps := mul_div_cancel₀ eps (zero_lt_one.trans_le hk1).ne'
  have hd : 0 < d := by
    have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
    exact div_pos hbl (by positivity)
  have hQdensity : bq*(Nat.card (G ⧸ K) : ℝ)^(-beta) ≤ (Q.length : ℝ)/Nat.card (G ⧸ K) :=
    (length_bound_iff_density_bound bq (Nat.card (G ⧸ K)) beta Q.length hqpos).mp
      (by simpa only [beta,k,Nat.cast_add,Nat.cast_one] using hQ)
  let h := Nat.card (K ⧸ B.subgroupOf K)
  have hfactor : (Nat.card G : ℝ) = (Nat.card (G ⧸ K) : ℝ)*h*Nat.card B := by
    exact_mod_cast elementClosure_card_factorization a
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.card_pos (α := K ⧸ B.subgroupOf K))
  have hB1 : (1 : ℝ) ≤ Nat.card B := by exact_mod_cast (Nat.card_pos (α := B))
  have hcycle : ∃ C : Cycle (CayleyDigraph A),
      b*(Nat.card G : ℝ)^(1-eps) ≤ C.length ∧ C.ClosedUnderGenerator a ∧
      (AbovePrimeCutoff G (n+1) → SpansTruncation (n+1) (C.generatorTails a)) := by
    by_cases hp : AbovePrimeCutoff G (n+1)
    · have hpQ := hp.of_card_dvd K.card_quotient_dvd_card
      obtain ⟨C,hC,hCa,hspan⟩ := spanning_cycle_lift a A ha n (hc.trans hcn) hh Q (hQspan hpQ)
        bl eps hbl.le hlayer hp
      have hGqK : (Nat.card G : ℝ) = (Nat.card (G ⧸ K) : ℝ)*Nat.card K := by
        exact_mod_cast K.card_eq_card_quotient_mul_card_subgroup
      have hlinear : (bl/4)*((Q.length : ℝ)/Nat.card (G ⧸ K))*(Nat.card B : ℝ)^(-eps) ≤
          (C.length : ℝ)/Nat.card G := by
        have hdiv := div_le_div_of_nonneg_right hC hGpos.le
        apply le_trans (le_of_eq ?_) hdiv
        rw [hGqK]
        field_simp
        change (Q.length : ℝ)*(Nat.card B : ℝ)^(-eps)*Nat.card K =
          (Q.length : ℝ)*Nat.card K*(Nat.card B : ℝ)^(-eps)
        ring
      have hQweak := density_bound_weaken bq bq beta eps (Nat.card (G ⧸ K)) _ hbq.le le_rfl hbetaeps hq1 hQdensity
      have hcalc := large_kernel_density bq (bl/4) (Nat.card (G ⧸ K)) h (Nat.card B)
        (Nat.card G) eps eps Q.length ((C.length : ℝ)/Nat.card G) 1 hbq.le (by positivity)
        hqpos hh1 hB1 hfactor heps (by norm_num) hQweak (by simpa only [pow_one] using hlinear)
      simp only [Nat.cast_one,one_mul,pow_one] at hcalc
      have hweak := density_bound_weaken (bl/4*bq) b eps eps (Nat.card G) _ (by positivity)
        (min_le_right _ _) le_rfl hG1 hcalc
      exact ⟨C,(length_bound_iff_density_bound b (Nat.card G) eps C.length hGpos).mpr hweak,hCa,fun _ => hspan⟩
    · obtain ⟨C,hCa,hC⟩ := directed_cycle_lifting a A ha r c n hr hc hcn hh Q bl eps hbl heps hsub
      have hcalc := large_kernel_density bq d (Nat.card (G ⧸ K)) h (Nat.card B)
        (Nat.card G) beta eps Q.length ((C.length : ℝ)/Nat.card G) k hbq.le hd.le
        hqpos hh1 hB1 hfactor heps heq.ge hQdensity hC
      rw [heq] at hcalc
      have hweak := density_bound_weaken (d*bq^k) b eps eps (Nat.card G) _ (by positivity)
        (min_le_left _ _) le_rfl hG1 hcalc
      exact ⟨C,(length_bound_iff_density_bound b (Nat.card G) eps C.length hGpos).mpr hweak,hCa,fun hp' => (hp hp').elim⟩
  obtain ⟨C,hC,hCa,hspan⟩ := hcycle
  obtain ⟨L,hL,hLspan⟩ := expand_cycle_into_rounds_spanning S xs hlen hxs C hCa
  refine ⟨L,?_,fun hp => hLspan (n+1) (hspan hp)⟩
  rw [hL,Nat.cast_mul]
  have hscaled := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg T)
  nlinarith only [hscaled]

end DirectedCycles
