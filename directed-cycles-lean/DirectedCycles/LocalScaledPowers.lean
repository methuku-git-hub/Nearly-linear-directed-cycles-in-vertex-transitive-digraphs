module

public import DirectedCycles.LocalSignedPowers
public import DirectedCycles.LocalGroupUltraproduct
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Floors at a bounded real fraction of an integer scale stay in the same
integer interval, including the negative endpoint. -/
theorem scaled_floor_natAbs_le (t : ℝ) (N : ℕ) (ht : |t| ≤ 1) :
    (Int.floor (t*(N : ℝ))).natAbs ≤ N := by
  have ht' := abs_le.mp ht
  have hlo : -(N : ℤ) ≤ Int.floor (t*(N : ℝ)) := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [mul_nonneg (by linarith : 0 ≤ t+1) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hhi : Int.floor (t*(N : ℝ)) ≤ (N : ℤ) := by
    apply Int.floor_le_iff.mpr
    push_cast
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  omega

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*)
    (L : ∀ i, LocalGroupAlgebra (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))

/-- Bounded scaled powers taken from actual finite local power segments. -/
noncomputable def localScaledPower (t : ℝ) : LocalUltraproduct (U : Filter ι) G :=
  localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (Int.floor (t*(N i : ℝ))))

theorem localScaledPower_zero : localScaledPower U G L u N M p 0 =
    (localUltraAlgebra (U : Filter ι) G L).one := by
  apply Quotient.sound
  exact Filter.Eventually.of_forall fun i => by
    simp only [zero_mul,Int.floor_zero,(p i).signedPower_zero]

theorem localScaledPower_one : localScaledPower U G L u N M p 1 =
    localUltraMk (U : Filter ι) G (fun i => (p i).power (N i)) := by
  apply Quotient.sound
  exact Filter.Eventually.of_forall fun i => by
    simp only [one_mul,Int.floor_natCast,(p i).signedPower_nat]

/-- The floor-addition defect is zero or one actual generator. Every partial
product is certified using the component power segments. -/
theorem localScaledPower_add_cases (hd : ∀ i, (L i).DivisionClosed)
    (hr : ∀ i, (L i).Reversible)
    (hN : ∀ᶠ i in (U : Filter ι), 1 ≤ N i ∧ 2*N i ≤ M i)
    (s t : ℝ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) (hst : |s+t| ≤ 1) :
    (localUltraAlgebra (U : Filter ι) G L).mulRel
      (localScaledPower U G L u N M p s) (localScaledPower U G L u N M p t)
      (localScaledPower U G L u N M p (s+t)) ∨
    ∃ z, (localUltraAlgebra (U : Filter ι) G L).mulRel
      (localScaledPower U G L u N M p s) (localScaledPower U G L u N M p t) z ∧
      (localUltraAlgebra (U : Filter ι) G L).mulRel z (localUltraMk (U : Filter ι) G u)
        (localScaledPower U G L u N M p (s+t)) := by
  let a : ι → ℤ := fun i => Int.floor (s*(N i : ℝ))
  let b : ι → ℤ := fun i => Int.floor (t*(N i : ℝ))
  let c : ι → ℤ := fun i => Int.floor ((s+t)*(N i : ℝ))
  have ha : ∀ i, (a i).natAbs ≤ N i := fun i => scaled_floor_natAbs_le s (N i) hs
  have hb : ∀ i, (b i).natAbs ≤ N i := fun i => scaled_floor_natAbs_le t (N i) ht
  have hc : ∀ i, (c i).natAbs ≤ N i := fun i => scaled_floor_natAbs_le (s+t) (N i) hst
  have hab : ∀ i, (a i+b i).natAbs ≤ 2*N i := by
    intro i
    exact (Int.natAbs_add_le _ _).trans (by have := ha i; have := hb i; omega)
  have hcases : ∀ᶠ i in (U : Filter ι), c i = a i+b i ∨ c i = a i+b i+1 := by
    apply Filter.Eventually.of_forall
    intro i
    have h1 := Int.le_floor_add (s*(N i : ℝ)) (t*(N i : ℝ))
    have h2 := Int.le_floor_add_floor (s*(N i : ℝ)) (t*(N i : ℝ))
    rw [← add_mul] at h1 h2
    dsimp only [a,b,c]
    omega
  rcases Ultrafilter.eventually_or.mp hcases with he | he
  · left
    apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
    filter_upwards [hN,he] with i hNi hei
    change (L i).mulRel ((p i).signedPower (a i)) ((p i).signedPower (b i)) ((p i).signedPower (c i))
    rw [hei]
    exact (p i).signedPower_add (hd i) (hr i) (a i) (b i)
      (by have := ha i; omega) (by have := hb i; omega) ((hab i).trans hNi.2)
  · right
    refine ⟨localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (a i+b i)),?_,?_⟩
    · apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
      filter_upwards [hN] with i hNi
      exact (p i).signedPower_add (hd i) (hr i) (a i) (b i)
        (by have := ha i; omega) (by have := hb i; omega) ((hab i).trans hNi.2)
    · apply (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2
      filter_upwards [hN,he] with i hNi hei
      have hh := (p i).signedPower_add (hd i) (hr i) (a i+b i) 1
        ((hab i).trans hNi.2) (by simp; omega) (by rw [← hei]; have := hc i; omega)
      simpa only [← hei,show (p i).signedPower 1 = u i by
        simpa only [Int.natCast_one,(p i).one (by omega)] using (p i).signedPower_nat 1] using hh
end DirectedCycles
