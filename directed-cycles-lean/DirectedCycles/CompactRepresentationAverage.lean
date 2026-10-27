module

public import DirectedCycles.CompactRankOneAverage
public import DirectedCycles.CompactSpectralDetection
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

set_option autoImplicit false
open MeasureTheory InnerProductSpace
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : G →* E →L[ℝ] E)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace G] [CompleteSpace E] in
/-- Isometric conjugation transports the actual rank-one operator. -/
theorem rankOne_representation_transport
    (hinner : ∀ g u v, inner ℝ (R g u) (R g v) = inner ℝ u v) (g : G) (u : E) :
    (R g).comp (rankOne ℝ u u) = (rankOne ℝ (R g u) (R g u)).comp (R g) := by
  ext v
  change R g (inner ℝ u v • u) = inner ℝ (R g u) (R g v) • R g u
  rw [map_smul,hinner]

/-- Haar averaging makes the actual compact rank-one average commute
with every operator of the group representation. -/
theorem rankOneAverage_commutes
    (hc : ∀ v, Continuous (fun g => R g v))
    (hinner : ∀ g u v, inner ℝ (R g u) (R g v) = inner ℝ u v) (v : E) (g : G) :
    (R g).comp (rankOneAverage μ (fun h => R h v)) =
      (rankOneAverage μ (fun h => R h v)).comp (R g) := by
  let f : G → E →L[ℝ] E := fun h => rankOne ℝ (R h v) (R h v)
  have hf : Integrable f μ := (continuous_rankOne_self (hc v)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  let L := ContinuousLinearMap.compL ℝ E E E (R g)
  let K := (ContinuousLinearMap.compL ℝ E E E).flip (R g)
  have hL : L (∫ h, f h ∂μ) = ∫ h, L (f h) ∂μ := (L.integral_comp_comm hf).symm
  have hK : K (∫ h, f h ∂μ) = ∫ h, K (f h) ∂μ := (K.integral_comp_comm hf).symm
  change L (∫ h, f h ∂μ) = K (∫ h, f h ∂μ)
  rw [hL,hK]
  calc
    (∫ h, L (f h) ∂μ) = ∫ h, K (f (g*h)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro h
      change (R g).comp (rankOne ℝ (R h v) (R h v)) =
        (rankOne ℝ (R (g*h) v) (R (g*h) v)).comp (R g)
      rw [rankOne_representation_transport R hinner]
      have he : R g (R h v) = R (g*h) v :=
        (congrArg (fun A : E →L[ℝ] E => A v) (map_mul R g h)).symm
      rw [he]
    _ = ∫ h, K (f h) ∂μ := integral_mul_left_eq_self (fun h => K (f h)) g

omit [Group G] [IsTopologicalGroup G] [μ.IsMulLeftInvariant] in
/-- Each vector of a continuous family belongs to the closure of the
range of its rank-one average, provided the measure has full support. -/
theorem rankOneAverage_range_closure [μ.IsOpenPosMeasure]
    (f : G → E) (hf : Continuous f) (x : G) :
    f x ∈ (rankOneAverage μ f).range.topologicalClosure := by
  have hsym := rankOneAverage_symmetric μ f hf
  have hk : f x ∈ (rankOneAverage μ f).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact rankOneAverage_kernel_orthogonal μ f hf hv x
  have he := hsym.orthogonal_range
  change (rankOneAverage μ f).rangeᗮ = (rankOneAverage μ f).ker at he
  rw [← he] at hk
  simpa only [Submodule.orthogonal_orthogonal_eq_closure] using hk

omit [IsTopologicalGroup G] [μ.IsMulLeftInvariant] in
/-- A moved vector gives an averaged compact operator whose range is
not fixed by the same group element. No separating-operator hypothesis is added. -/
theorem rankOneAverage_detects [μ.IsOpenPosMeasure]
    (hc : ∀ v, Continuous (fun g => R g v)) {g : G} {v : E} (hne : R g v ≠ v) :
    (R g).comp (rankOneAverage μ (fun h => R h v)) ≠ rankOneAverage μ (fun h => R h v) := by
  intro he
  let T := rankOneAverage μ (fun h => R h v)
  let D : E →L[ℝ] E := R g-1
  have hker : T.range ≤ D.ker := by
    rintro w ⟨u,rfl⟩
    change R g (T u)-T u = 0
    exact sub_eq_zero.mpr (congrArg (fun A : E →L[ℝ] E => A u) he)
  have hcl := Submodule.topologicalClosure_minimal _ hker D.isClosed_ker
  have hv : v ∈ T.range.topologicalClosure := by
    have h := rankOneAverage_range_closure μ (fun h => R h v) (hc v) 1
    simpa only [map_one,one_apply_eq_self] using h
  exact hne (sub_eq_zero.mp (hcl hv))
end DirectedCycles
