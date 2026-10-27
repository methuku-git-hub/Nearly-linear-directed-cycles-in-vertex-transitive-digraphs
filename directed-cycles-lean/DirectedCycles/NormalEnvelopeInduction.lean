module

public import DirectedCycles.RelativeSeriesQuotients
public import DirectedCycles.FiniteEnvelopeReduction
public import DirectedCycles.QuotientPowerContainment

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The remaining terminal-layer construction for the finite normal-envelope
proof. This is a proposition to be proved, not an axiom or a theorem. -/
def FiniteTerminalPeeling : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∀ c n : ℕ, ∃ P : ℕ,
    ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.nilpotencyClass G ≤ c → ∀ A : Set G,
      IsApproximateSubgroup K A → Subgroup.closure A = ⊤ →
      ∀ H : Subgroup G, (H : Set G) ⊆ A →
      relativeSeries (Subgroup.normalClosure (H : Set G)) (n+1) = ⊥ →
      ∃ L : Subgroup G, L.Normal ∧
        relativeSeries (Subgroup.normalClosure (H : Set G)) n ≤ L ∧ (L : Set G) ⊆ A^P

/-- Once bounded terminal layers have been constructed uniformly, quotient
induction supplies the full normal envelope. All quotient, class, image,
and kernel-factor steps are proved here. -/
theorem finite_nilpotent_envelope_of_terminal_peeling (hPeel : FiniteTerminalPeeling) :
    FiniteNilpotentEnvelope := by
  intro K hK c
  have hheight : ∀ n : ℕ, ∃ C : ℕ, 1 ≤ C ∧
      ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
        Group.nilpotencyClass G ≤ c → ∀ A : Set G,
        IsApproximateSubgroup K A → Subgroup.closure A = ⊤ →
        ∀ H : Subgroup G, (H : Set G) ⊆ A →
        relativeSeries (Subgroup.normalClosure (H : Set G)) n = ⊥ →
        (Subgroup.normalClosure (H : Set G) : Set G) ⊆ A^C := by
    intro n
    induction n with
    | zero =>
      refine ⟨1,le_rfl,?_⟩
      intro G _ _ _ _hc A hA _hgen H _hH hz g hg
      change Subgroup.normalClosure (H : Set G) = ⊥ at hz
      rw [hz] at hg
      have he : g = 1 := hg
      simpa only [he,pow_one] using hA.one_mem
    | succ n ih =>
      obtain ⟨C,hC,hind⟩ := ih
      obtain ⟨P,hstep⟩ := hPeel K hK c n
      refine ⟨C+P,by omega,?_⟩
      intro G _ _ _ hc A hA hgen H hH hz
      obtain ⟨L,hLn,hRL,hLp⟩ := hstep G hc A hA hgen H hH hz
      let : L.Normal := hLn
      let q := QuotientGroup.mk' L
      have hq := QuotientGroup.mk'_surjective L
      let B := q '' A
      let J := H.map q
      have hB : IsApproximateSubgroup K B := hA.image q
      have hBgen : Subgroup.closure B = ⊤ := image_generating_set q hq A hgen
      have hJ : (J : Set (G ⧸ L)) ⊆ B := Set.image_mono hH
      have hheightQ : relativeSeries (Subgroup.normalClosure (J : Set (G ⧸ L))) n = ⊥ := by
        exact relativeSeries_quotient_eq_bot (H : Set G) L n hRL
      have hcQ : Group.nilpotencyClass (G ⧸ L) ≤ c :=
        (Group.nilpotencyClass_le_of_surjective q hq).trans hc
      have hbound := hind (G ⧸ L) hcQ B hB hBgen J hJ hheightQ
      have hmap : (Subgroup.normalClosure (H : Set G)).map q =
          Subgroup.normalClosure (J : Set (G ⧸ L)) := Subgroup.map_normalClosure _ q hq
      intro g hg
      have him : q g ∈ Subgroup.normalClosure (J : Set (G ⧸ L)) := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem q hg
      exact preimage_image_pow_subset q A C P (by simpa only [q,QuotientGroup.ker_mk'] using hLp)
        (hbound him)
  obtain ⟨C,hC,hproof⟩ := hheight c
  refine ⟨C,hC,?_⟩
  intro G _ _ _ hc A hA hgen H hH
  apply hproof G hc A hA hgen H hH
  apply le_antisymm _ bot_le
  exact (relativeSeries_le_lower (Subgroup.normalClosure (H : Set G)) c).trans
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc).le

end DirectedCycles
