module

public import DirectedCycles.TerminalWidthShortGenerators
public import DirectedCycles.CommutatorMapNaturality
public import DirectedCycles.CentralRankQuotient
public import DirectedCycles.NormalEnvelopeInduction

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

set_option maxHeartbeats 800000 in
/-- The finite terminal-layer construction from the exact weak abelian
inverse input. In particular no unproved commutator decomposition or
normal-generation assumption enters the quotient induction. -/
theorem finite_terminal_peeling_of_abelian_input (hAb : FiniteAbelianShortGeneration) :
    FiniteTerminalPeeling := by
  classical
  intro K hK _c n
  let p := 4^(n+1)*4
  have hp : 2 ≤ p := by
    have hpow : 0 < 4^(n+1) := by positivity
    dsimp [p]
    omega
  obtain ⟨r,hcentral⟩ := central_rank_quotient_of_abelian_input hAb K hK p hp
  obtain ⟨d,hgenerators⟩ := abelianization_short_generators hAb K hK
  let E := (d+1)^n*(p*r)
  refine ⟨E+p*4,?_⟩
  intro G _ _ _ _hc A hA hgen H hH hnext
  obtain ⟨Z,hZn,_hZc,hZpow,T,hTc,hr,hT⟩ := hcentral G A hA
  let : Z.Normal := hZn
  let q := QuotientGroup.mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  let B := q '' A
  let J := H.map q
  let N := Subgroup.normalClosure (H : Set G)
  let NQ := Subgroup.normalClosure (J : Set (G ⧸ Z))
  have hB : IsApproximateSubgroup K B := hA.image q
  have hBgen : Subgroup.closure B = ⊤ := image_generating_set q hq A hgen
  have hseries : ∀ m, relativeSeries NQ m = (relativeSeries N m).map q :=
    fun m => normalClosure_image_relativeSeries q hq (H : Set G) m
  have hnextQ : relativeSeries NQ (n+1) = ⊥ := by
    rw [hseries,hnext,Subgroup.map_bot]
  obtain ⟨U,k,x,hk,hU,hx,hUgen⟩ := hgenerators (G ⧸ Z) B hB hBgen
  let l := List.ofFn (fun i : Fin n => i)
  have hlen : l.length = n := List.length_ofFn
  have hl : l.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hall : ∀ i : Fin n, i ∈ l := by intro i; simp [l]
  let w := MarkedCommutatorWord.leftList l
  have hdegree : w.degree = n := by simp [w,hlen]
  have hw : w.leafLabels.Nodup := by simpa [w] using hl
  have hwAll : ∀ i, i ∈ w.leafLabels := by simpa [w] using hall
  have hnextW : relativeSeries NQ (w.degree+1) = ⊥ := by rw [hdegree]; exact hnextQ
  have hshort : ∀ h : J, ∀ y : Fin n → G ⧸ Z, (∀ i, y i ∈ B^4) →
      w.eval h.val y ∈ T ∧ w.eval h.val y ∈ B^p := by
    intro h y hy
    have hv := w.short_values_lift q H A hA.one_mem hA.inv_eq_self hH
      (by rw [hdegree]; exact hnext) h.val h.property y hy
    rw [hdegree] at hv
    change w.eval h.val y ∈ q '' (A^p ∩ (Subgroup.center G : Set G)) at hv
    refine ⟨hT hv,?_⟩
    rw [← Set.image_pow]
    exact Set.image_mono Set.inter_subset_left hv
  have hwidth := w.terminal_width_of_short_generators J hw hwAll hnextW
    B U k x hU hx hUgen T hTc r p hr hshort
  have hclosure : Subgroup.closure (Set.range (w.subgroupTerminalMultihom J hw hwAll hnextW)) =
      relativeSeries NQ n := by
    have hc := MarkedCommutatorWord.subgroupTerminalMultihom_closure J l hl hall
      (by rw [hlen]; exact hnextQ)
    simpa only [hlen] using hc
  rw [hclosure,Fintype.card_fin] at hwidth
  let L := (relativeSeries NQ n).comap q
  refine ⟨L,inferInstance,?_,?_⟩
  · intro g hg
    change q g ∈ relativeSeries NQ n
    rw [hseries]
    exact Subgroup.mem_map_of_mem q hg
  · intro g hg
    have hm : (k+1)^n*(p*r) ≤ E :=
      Nat.mul_le_mul_right (p*r) (Nat.pow_le_pow_left (by omega) n)
    have hbpow : q g ∈ B^E := Set.pow_subset_pow_right hB.one_mem hm (hwidth hg)
    exact preimage_image_pow_subset q A E (p*4)
      (by simpa only [q,QuotientGroup.ker_mk'] using hZpow) hbpow

/-- Complete finite normal-envelope deduction from the weak abelian
inverse theorem; the inverse theorem itself is still an explicit premise. -/
theorem finite_nilpotent_envelope_of_abelian_input (hAb : FiniteAbelianShortGeneration) :
    FiniteNilpotentEnvelope :=
  finite_nilpotent_envelope_of_terminal_peeling (finite_terminal_peeling_of_abelian_input hAb)

end DirectedCycles
