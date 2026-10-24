import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- The actual left regular representation on real square-integrable
functions, using inverse translation of the variable. -/
noncomputable def leftRegularRepresentation : G →* Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ where
  toFun g :=
    { toFun := fun v => DomMulAct.mk g⁻¹ • v
      map_add' := smul_add _
      map_smul' := fun c v => smul_comm _ c v
      cont := continuous_const_smul _ }
  map_one' := by ext v; simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro v
    change DomMulAct.mk (g*h)⁻¹ • v = DomMulAct.mk g⁻¹ • (DomMulAct.mk h⁻¹ • v)
    rw [mul_inv_rev,DomMulAct.mk_mul]
    exact @SemigroupAction.mul_smul Gᵈᵐᵃ (Lp ℝ 2 μ) _
      (inferInstance : MulAction Gᵈᵐᵃ (Lp ℝ 2 μ)).toSemigroupAction
      (DomMulAct.mk g⁻¹) (DomMulAct.mk h⁻¹) v

omit [T2Space G] in
/-- The left regular action is strongly continuous. -/
theorem leftRegularRepresentation_continuous (v : Lp ℝ 2 μ) :
    Continuous (fun g => leftRegularRepresentation μ g v) := by
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  exact (DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const

omit [T2Space G] [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
/-- Translation preserves the Hilbert inner product. -/
theorem leftRegularRepresentation_inner (g : G) (u v : Lp ℝ 2 μ) :
    inner ℝ (leftRegularRepresentation μ g u) (leftRegularRepresentation μ g v) = inner ℝ u v := by
  apply (LinearMap.norm_map_iff_inner_map_map (leftRegularRepresentation μ g)).mp
  intro w
  exact DomMulAct.norm_smul_Lp _ w

omit [T2Space G] [μ.InnerRegularCompactLTTop] in
/-- Compatibility with actual continuous functions, before quotienting
by almost-everywhere equality. -/
theorem leftRegularRepresentation_continuous_function [CompactSpace G]
    (g : G) (f : C(G,ℝ)) :
    leftRegularRepresentation μ g (ContinuousMap.toLp 2 μ ℝ f) =ᵐ[μ]
      (fun x => f (g⁻¹*x)) := by
  have h₁ := DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g⁻¹) (ContinuousMap.toLp 2 μ ℝ f)
  have h₂ := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f)
  exact h₁.trans h₂

omit [μ.InnerRegularCompactLTTop] in
/-- Every nonidentity translation moves a real continuous function and
therefore moves a vector of the regular Hilbert representation. -/
theorem leftRegularRepresentation_faithful [CompactSpace G] [μ.IsOpenPosMeasure]
    (g : G) (hg : g ≠ 1) : ∃ v : Lp ℝ 2 μ, leftRegularRepresentation μ g v ≠ v := by
  have hginv : g⁻¹ ≠ 1 := inv_ne_one.mpr hg
  obtain ⟨f,hf1,hfg,_⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({1} : Set G))
    (isClosed_singleton : IsClosed ({g⁻¹} : Set G))
    (Set.disjoint_singleton.mpr (Ne.symm hginv))
  refine ⟨ContinuousMap.toLp 2 μ ℝ f,?_⟩
  intro he
  have hae := (leftRegularRepresentation_continuous_function μ g f).symm
  rw [he] at hae
  have hall := μ.eq_of_ae_eq (hae.trans (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f))
    (f.continuous.comp (continuous_const.mul continuous_id)) f.continuous
  have h := congrFun hall 1
  have ha : f 1 = 0 := hf1 (Set.mem_singleton 1)
  have hb : f g⁻¹ = 1 := hfg (Set.mem_singleton g⁻¹)
  simp only [mul_one,ha,hb] at h
  exact one_ne_zero h
end DirectedCycles
