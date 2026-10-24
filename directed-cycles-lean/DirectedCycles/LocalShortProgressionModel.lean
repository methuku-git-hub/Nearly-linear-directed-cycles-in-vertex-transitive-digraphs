import DirectedCycles.LocalScaledExponentLimit
import DirectedCycles.ClampedExponentLimit
import DirectedCycles.ShortProgressionModelImage

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
namespace LocalGroupAlgebra.PowerSegment
variable {G : Type*} {L : LocalGroupAlgebra G} {u : G} {M : ℕ}

/-- The actual signed segment strictly before the specified first-exit index.
The caller proves that this index lies within the certified power segment. -/
def shortSignedSet (p : L.PowerSegment u M) (N : ℕ) : Set G :=
  {x | ∃ k : ℤ, k.natAbs < N ∧ p.signedPower k = x}
end LocalGroupAlgebra.PowerSegment

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The image of the actual internal local first-exit progression is exactly
the closed unit curve segment. Normalized-exponent compactness proves one
inclusion; clamped interior exponents prove the endpoints and the other. -/
theorem local_shortProgression_model_image_eq {H : Type*} [Group H]
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (φ : ℝ → H)
    (hformula : ∀ t : ℝ, |t| ≤ 1 → φ t = π.toFun (localScaledPower U G L u N M p t)) :
    π.toFun '' localUltraSet (U : Filter ι) G (fun i => (p i).shortSignedSet (N i)) =
      φ '' Set.Icc (-1 : ℝ) 1 := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    obtain ⟨v,rfl⟩ := Quotient.exists_rep z
    have hvm := (localUltraMk_mem_iff (U : Filter ι) G (fun i => (p i).shortSignedSet (N i)) v).1 hz
    have hc : ∀ i, ∃ k : ℤ, v i ∈ (p i).shortSignedSet (N i) →
        k.natAbs < N i ∧ (p i).signedPower k = v i := by
      intro i
      by_cases h : v i ∈ (p i).shortSignedSet (N i)
      · obtain ⟨k,hk,he⟩ := h
        exact ⟨k,fun _ => ⟨hk,he⟩⟩
      · exact ⟨0,fun hh => (h hh).elim⟩
    choose k hk using hc
    have hkN : ∀ᶠ i in (U : Filter ι), (k i).natAbs < N i := hvm.mono fun i hi => (hk i hi).1
    have he : localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i)) =
        localUltraMk (U : Filter ι) G v :=
      Quotient.sound (hvm.mono fun i hi => (hk i hi).2)
    obtain ⟨t,ht,hlim⟩ := short_exponent_has_ultralimit U N k (hN 0) hkN
    have hm := local_model_scaled_exponent_limit U G L hd hr A u N M p k t hN hM hi hprev
      hkN (abs_le.mpr ht) hlim π V hNSS himage
    rw [he,← hformula t (abs_le.mpr ht)] at hm
    exact ⟨t,ht,hm.symm⟩
  · rintro y ⟨t,ht,rfl⟩
    let k : ι → ℤ := fun i => clampedScaledExponent t (N i)
    let a := localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))
    have hkN : ∀ᶠ i in (U : Filter ι), (k i).natAbs < N i :=
      (hN 0).mono fun i hni => clampedScaledExponent_natAbs_lt t hni
    have ha : a ∈ localUltraSet (U : Filter ι) G (fun i => (p i).shortSignedSet (N i)) :=
      (localUltraMk_mem_iff (U : Filter ι) G _ _).2 (hkN.mono fun i hki => ⟨k i,hki,rfl⟩)
    have hm := local_model_scaled_exponent_limit U G L hd hr A u N M p k t hN hM hi hprev
      hkN (abs_le.mpr ht) (clamped_exponent_tendsto U N hN t (abs_le.mpr ht)) π V hNSS himage
    exact ⟨a,ha,hm.trans (hformula t (abs_le.mpr ht)).symm⟩
end DirectedCycles
