import DirectedCycles.NilpotentLargeRound
import DirectedCycles.NilpotentBoundedRounds
import DirectedCycles.LowerClassInputs
import DirectedCycles.BaselineHamiltonian
import DirectedCycles.SubsingletonLayers
import DirectedCycles.PrimeCutoffFactors

set_option autoImplicit false
universe u
namespace DirectedCycles

/-- The current-class layer estimate follows from the current-class Cayley
estimate and lower-class layer estimates, with uniform constants and spanning. -/
theorem layer_bound_from_cayley_and_lower (r c n : ℕ) (hcn : c ≤ n)
    (hcurrent : ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 < b ∧
      ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
        Group.rank H ≤ r → Group.nilpotencyClass H ≤ c → CayleySpanningBound H (n+1) b eta)
    (hlower : ∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 < b ∧
      ∀ (H : Type u) [Group H] [Finite H] [Group.IsNilpotent H],
        Group.rank H ≤ ∑ i ∈ Finset.range c,r^(i+1) →
        Group.nilpotencyClass H ≤ c/2 → LayerSpanningBound H (n+1) b eta)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℝ, 0 < b ∧ ∀ (G : Type u) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.rank G ≤ r → Group.nilpotencyClass G ≤ c → LayerSpanningBound G (n+1) b eps := by
  let k := auxiliaryIndexExponent r c n+1
  have hk : (0 : ℝ) < auxiliaryIndexExponent r c n+1 := by positivity
  obtain ⟨bq,hbq,hqbound⟩ := hcurrent (eps/(auxiliaryIndexExponent r c n+1)) (div_pos heps hk)
  obtain ⟨bl,hbl,hlbound⟩ := hlower eps heps
  let big := min (bl/(4*(auxiliaryIndexConstant r c n : ℝ))*bq^k) (bl/4*bq)
  have hbig : 0 < big := by
    have hJ : (0 : ℝ) < auxiliaryIndexConstant r c n := by exact_mod_cast auxiliaryIndexConstant_pos r c n
    exact lt_min (mul_pos (div_pos hbl (by positivity)) (pow_pos hbq k)) (by positivity)
  let Mnat := ((8*(n+1)+4)^(c*∑ i ∈ Finset.range c,r^(i+1))).factorial^
    (∑ i ∈ Finset.range c,r^(i+1))
  have hMnat : 0 < Mnat := pow_pos (Nat.factorial_pos _) _
  have hM : (0 : ℝ) < Mnat := by exact_mod_cast hMnat
  let b : ℝ := min (Mnat : ℝ)⁻¹ (min 1 big)
  have hb : 0 < b := lt_min (inv_pos.mpr hM) (lt_min (by norm_num) hbig)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hbbig : b ≤ big := (min_le_right _ _).trans (min_le_right _ _)
  have hbM : b*(Mnat : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (min_le_left ((Mnat : ℝ)⁻¹) (min 1 big)) hM.le
    rwa [inv_mul_cancel₀ hM.ne'] at h
  refine ⟨b,hb,?_⟩
  intro G _ _ _ hr hc T hT S _ hsc
  let : NeZero T := ⟨by omega⟩
  have hpow := cardinal_rpow_le_card (G := G) eps heps.le
  have hcardpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  rcases subsingleton_or_nontrivial G with hG | hG
  · let : Subsingleton G := hG
    obtain ⟨L,hL,hs⟩ := subsingleton_layer_hamiltonian hT S hsc
    refine ⟨L,?_,?_⟩
    · have hcG : Nat.card G = 1 := Nat.card_unique
      rw [hcG,Nat.cast_one,Real.one_rpow,mul_one]
      have hm := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg T)
      have hL' : (T : ℝ) ≤ L.length := by exact_mod_cast hL
      simp only [one_mul] at hm
      exact hm.trans hL'
    · intro _ z
      have hfull : L.layerCoordinates z = Set.univ := Set.eq_univ_of_forall (fun x => hs (x,z))
      rw [hfull]
      exact spansTruncation_univ (n+1)
  · let : Nontrivial G := hG
    by_cases hlarge : ∃ t ∈ layerRoundProducts S, 8*(n+1)+4 <
        Nat.card (elementClosure t ⧸ (elementCommutators t).subgroupOf (elementClosure t))
    · obtain ⟨t,⟨xs,hlen,hxs,he⟩,ht⟩ := hlarge
      subst t
      by_cases hK : elementClosure xs.prod = ⊤
      · have hgen := elementClosure_eq_top_implies_cyclic xs.prod hK
        obtain ⟨L,hL,hfull⟩ := generating_baseline_hamiltonian S xs hlen hxs hgen
        refine ⟨L,?_,?_⟩
        · rw [hL,Nat.cast_mul]
          calc
            b*T*(Nat.card G : ℝ)^(1-eps) ≤ b*T*Nat.card G :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hb.le (Nat.cast_nonneg T))
            _ ≤ (T : ℝ)*Nat.card G := by
              have hm := mul_le_mul_of_nonneg_right hb1 (mul_nonneg (Nat.cast_nonneg T) hcardpos.le)
              simpa only [mul_assoc,one_mul] using hm
        · intro _ z
          rw [hfull]
          exact spansTruncation_univ (n+1)
      · let B := elementCommutators xs.prod
        let K := elementClosure xs.prod
        have hrQ : Group.rank (G ⧸ K) ≤ r :=
          (Group.rank_le_of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)).trans hr
        have hcQ : Group.nilpotencyClass (G ⧸ K) ≤ c := (Group.nilpotencyClass_quotient_le K).trans hc
        have hrB := nilpotent_subgroup_rank_bound r c hr hc B
        have hcB := commutator_subgroup_class_le_half B (elementCommutators_le_derived xs.prod) c hc
        have hsub : ∀ U : Subgroup B, LayerCycleLowerBound U bl eps := by
          intro U
          obtain ⟨hrU,hcU⟩ := elementCommutators_subgroup_bounds xs.prod r c hr hc U
          exact (hlbound U hrU hcU).to_lower_bound
        obtain ⟨L,hL,hspan⟩ := nilpotent_large_round_cycle S xs hlen hxs r c n hr hc hcn ht hK
          bq bl eps hbq hbl heps.le (hqbound (G ⧸ K) hrQ hcQ) (hlbound B hrB hcB) hsub hsc
        refine ⟨L,?_,hspan⟩
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbbig (Nat.cast_nonneg T))
          (Real.rpow_nonneg hcardpos.le _)).trans hL
    · have hf : ∀ t ∈ layerRoundProducts S,
          Nat.card (elementClosure t ⧸ (elementCommutators t).subgroupOf (elementClosure t)) ≤ 8*(n+1)+4 := by
        intro t ht
        by_contra hh
        exact hlarge ⟨t,ht,by omega⟩
      have hcard := nilpotent_card_of_bounded_round_factors S hsc r c (8*(n+1)+4) hr hc hf
      obtain ⟨L,hL⟩ := stronglyConnected_layer_cycle hT S hsc
      refine ⟨L,?_,?_⟩
      · have hcard' : (Nat.card G : ℝ) ≤ Mnat := by exact_mod_cast hcard
        have hm := (mul_le_mul_of_nonneg_left (hpow.trans hcard') hb.le).trans hbM
        have hscaled := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg T)
        have hL' : (T : ℝ) ≤ L.length := by exact_mod_cast hL
        nlinarith only [hscaled,hL']
      · intro hp
        obtain ⟨t,ht,ht1⟩ := generating_set_nonidentity (layerRoundProducts S)
          (cyclicLayer_rounds_generate S hsc)
        exact False.elim (not_lt_of_ge (hf t ht) (hp.elementClosure_factor_large t ht1))

end DirectedCycles
