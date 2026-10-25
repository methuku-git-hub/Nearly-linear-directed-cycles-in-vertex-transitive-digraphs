module

public import DirectedCycles.LocalInfinitesimalPowers
public import DirectedCycles.LocalBoundedScaledPowers
public import DirectedCycles.ScaledExponentLimit

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- The image of an actual bounded signed power depends only on the real
limit of its normalized exponent. The difference power is constructed in the
doubled local segment and killed by the proved infinitesimal NSS lemma. -/
theorem local_model_scaled_exponent_limit_bounded {H : Type*} [Group H]
    (C : ℕ) (hC : 1 ≤ C)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i)) (k : ι → ℤ) (t : ℝ)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), 2*(C*N i) ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hk : ∀ᶠ i in (U : Filter ι), (k i).natAbs ≤ C*N i) (ht : |t| ≤ (C : ℝ))
    (hlim : Filter.Tendsto (fun i => (k i : ℝ)/(N i : ℝ)) (U : Filter ι) (𝓝 t))
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (V : Set H) (hNSS : ∀ x : H, (∀ n : ℕ, x^n ∈ V) → x = 1)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))) =
      π.toFun (localScaledPower U G L u N M p t) := by
  let a := localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))
  let b := localScaledPower U G L u N M p t
  let d : ι → ℤ := fun i => k i-Int.floor (t*(N i : ℝ))
  have hNi : ∀ᶠ i in (U : Filter ι), 0 < N i ∧ N i ≤ M i := by
    filter_upwards [hN 0,hM] with i hni hmi
    exact ⟨hni,(Nat.le_mul_of_pos_left _ (by omega : 0 < C)).trans (by omega)⟩
  have hkill := local_map_infinitesimal_signed_power U G L hd hr A u N M p d hNi hi hprev
    (scaled_exponent_difference_small U N k t hN hlim) π V hNSS himage
  have hmul : (localUltraAlgebra (U : Filter ι) G L).mulRel a
      ((localUltraAlgebra (U : Filter ι) G L).inv b)
      (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (d i))) := by
    apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
    filter_upwards [hM,hk] with i hmi hki
    have hb := scaled_floor_natAbs_le_mul t (N i) C ht
    have hdb : (d i).natAbs ≤ M i := by
      have hh := Int.natAbs_add_le (k i) (-Int.floor (t*(N i : ℝ)))
      simp only [Int.natAbs_neg] at hh
      dsimp only [d]
      rw [sub_eq_add_neg]
      omega
    have hh := (p i).signedPower_add (hd i) (hr i) (k i) (-Int.floor (t*(N i : ℝ)))
      (by omega) (by simpa only [Int.natAbs_neg] using (show (Int.floor (t*(N i : ℝ))).natAbs ≤ M i by omega))
      (by simpa only [sub_eq_add_neg,d] using hdb)
    simpa only [(p i).signedPower_neg,sub_eq_add_neg,d] using hh
  have he := π.map_mul hmul
  change π.toFun a*π.toFun ((localUltraAlgebra (U : Filter ι) G L).inv b) =
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (d i))) at he
  rw [π.map_inv,hkill] at he
  exact mul_inv_eq_one.mp he
end DirectedCycles
