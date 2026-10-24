import DirectedCycles.FiniteTriplingStructure
import DirectedCycles.QuotientPowerContainment

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite graph structural theorem reduces to precisely two explicit
finite algebra assertions. Neither assertion is supplied as an axiom.
This proof avoids the locally compact and Lie-group reductions used in the
infinite-graph statement. -/
theorem finite_tripling_from_algebra (hBGT : FiniteApproximateStructure)
    (hEnvelope : FiniteNormalEnvelope) : FiniteTriplingStructure := by
  intro K hK
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK3 : (1 : ℝ) ≤ (K : ℝ)^3 := one_le_pow₀ hKreal
  obtain ⟨r,c,I,n₀,hI,hn₀,hBGT⟩ := hBGT ((K : ℝ)^3) hK3
  obtain ⟨C,hC,hEnvelope⟩ := hEnvelope ((K : ℝ)^3) hK3 c I
  refine ⟨I,r,c,I,2*C+8,n₀,hI,by omega,hn₀,?_⟩
  intro G V _ _ _ _ R e hsym hinv htrans hconn m hm htrip
  have hm1 : 1 ≤ m := hn₀.trans hm
  let S : Set G := actionStepSet R e
  have hS1 : (1 : G) ∈ S := actionStepSet_one R e
  have hSi : S⁻¹ = S := actionStepSet_inv R e hsym hinv
  have hSgen : Subgroup.closure S = ⊤ := actionStepSet_generates R e hinv htrans hconn
  have happrox : IsApproximateSubgroup ((K : ℝ)^3) (S^(2*m)) :=
    action_ball_approximate R e hsym hinv htrans m hm1 K (by exact_mod_cast htrip)
  obtain ⟨H,N,hH,hN,hHN,hHball,hNil,hr,hc,hindex⟩ :=
    hBGT G S hS1 hSi hSgen (2*m) (by omega) happrox
  let : H.Normal := hH
  let : N.Normal := hN
  let : Group.IsNilpotent (N ⧸ H.comap N.subtype) := hNil
  let Q := G ⧸ H
  let π : G →* Q := QuotientGroup.mk' H
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective H
  have hπker : π.ker = H := QuotientGroup.ker_mk' H
  let T : Set Q := π '' S
  let M : Subgroup Q := N.map π
  let : M.Normal := Subgroup.Normal.map inferInstance π hπ
  have hker : H ≤ π.ker := by rw [QuotientGroup.ker_mk']
  obtain ⟨hMNil,hrM,hcM⟩ := nilpotent_image_quotient_bounds π N H hker
  let : Group.IsNilpotent M := hMNil
  have hMind : M.index ≤ I :=
    (Nat.le_of_dvd (show 0 < N.index by rw [Subgroup.index_eq_card]; exact Nat.card_pos)
      (N.index_map_dvd hπ)).trans hindex
  have hT1 : (1 : Q) ∈ T := ⟨1,hS1,map_one π⟩
  have hTi : T⁻¹ = T := by
    dsimp only [T]
    rw [← Set.image_inv,hSi]
  have hTgen : Subgroup.closure T = ⊤ := image_generating_set π hπ S hSgen
  have hTapprox : IsApproximateSubgroup ((K : ℝ)^3) (T^(2*m)) := by
    simpa only [Set.image_pow] using happrox.image π
  let J : Subgroup Q := (N ⊓ MulAction.stabilizer G e).map π
  have hJM : J ≤ M := Subgroup.map_mono inf_le_left
  have hJball : (J : Set Q) ⊆ T^(2*m) := by
    rintro q ⟨g,hg,rfl⟩
    have hgS : g ∈ S := Or.inl hg.2
    exact Set.subset_pow hT1 (by omega : 2*m ≠ 0) ⟨g,hgS,rfl⟩
  have hEnvelopeBound := hEnvelope Q T hT1 hTi hTgen M (hcM.trans hc) hMind
    (2*m) (by omega) hTapprox J hJM hJball
  let L := (Subgroup.normalClosure (J : Set Q)).comap π
  have hkerN : π.ker ≤ N := by rw [QuotientGroup.ker_mk']; exact hHN
  obtain ⟨hkerL,hLN,hstab⟩ := quotient_stabilizer_envelope π hπ N hkerN e htrans
  have hHL : H ≤ L := by rw [hπker] at hkerL; exact hkerL
  have hLball : (L : Set G) ⊆ S^((2*C+8)*m) := by
    intro g hg
    have himage : π g ∈ T^(C*(2*m)) := hEnvelopeBound hg
    have hkb : (π.ker : Set G) ⊆ S^(4*(2*m)) := by
      rw [hπker]
      exact hHball
    have hh := preimage_image_pow_subset π S (C*(2*m)) (4*(2*m)) hkb himage
    convert hh using 1
    congr 1
    ring
  refine ⟨L,inferInstance,hLball,?_⟩
  exact induced_structure_of_collapse N H L hHL hLN hstab r c I hr hc hindex

end DirectedCycles
