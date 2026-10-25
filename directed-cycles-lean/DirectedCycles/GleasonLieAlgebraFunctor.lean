module

public import DirectedCycles.GleasonExponentialMap

@[expose] public section

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles
namespace OneParameter
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

theorem comp_productApprox (F : ContinuousMonoidHom G H) (φ ψ : OneParameter G)
    (t : ℝ) (n : ℕ) :
    productApprox (F.comp φ) (F.comp ψ) t n = F (φ.productApprox ψ t n) := by
  change (F (φ.eval (t/(n : ℝ)))*F (ψ.eval (t/(n : ℝ))))^n = F ((φ.eval (t/(n : ℝ))*ψ.eval (t/(n : ℝ)))^n)
  rw [map_pow,map_mul]

/-- Continuous group homomorphisms preserve the actual Trotter limits. -/
theorem IsTrotterSum.comp {φ ψ ζ : OneParameter G} (h : IsTrotterSum φ ψ ζ)
    (F : ContinuousMonoidHom G H) : IsTrotterSum (F.comp φ) (F.comp ψ) (F.comp ζ) := by
  obtain ⟨δ,hδ,hlim⟩ := h
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have h := F.continuous.tendsto (ζ.eval t) |>.comp (hlim t ht)
  change Tendsto (fun n => productApprox (F.comp φ) (F.comp ψ) t n) atTop (𝓝 (F (ζ.eval t)))
  simp only [comp_productApprox]
  exact h

theorem comp_scale (F : ContinuousMonoidHom G H) (c : ℝ) (φ : OneParameter G) :
    F.comp (scale c φ) = scale c (F.comp φ) := by
  apply ContinuousMonoidHom.ext
  intro t
  rfl
end OneParameter
namespace GleasonLieAlgebra
variable {G H J : Type*} [Group G] [Group H] [Group J]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
    (D : GleasonMetricData G) (E : GleasonMetricData H) (I : GleasonMetricData J)
    [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J]
    [LocallyCompactSpace G] [LocallyCompactSpace H] [LocallyCompactSpace J]

/-- The differential-space map is built directly by composing genuine
one-parameter subgroups; its linearity follows from the proved limit laws. -/
noncomputable def map (F : ContinuousMonoidHom G H) :
    GleasonLieAlgebra D →L[ℝ] GleasonLieAlgebra E where
  toFun x := F.comp (toOneParameter D x)
  map_add' x y := by
    let : MetricSpace H := E.compatibleMetric
    exact ((D.trotterSum_spec x y).comp F).unique (E.trotterSum_spec _ _)
  map_smul' c x := OneParameter.comp_scale F c x
  cont := F.continuous_comp_right

theorem map_eval (F : ContinuousMonoidHom G H) (x : GleasonLieAlgebra D) (t : ℝ) :
    (toOneParameter E (map D E F x)).eval t = F ((toOneParameter D x).eval t) := rfl

theorem exp_map (F : ContinuousMonoidHom G H) (x : GleasonLieAlgebra D) :
    exp E (map D E F x) = F (exp D x) := rfl

theorem map_comp (F : ContinuousMonoidHom G H) (Q : ContinuousMonoidHom H J) :
    map D I (Q.comp F) = (map E I Q).comp (map D E F) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousMonoidHom.ext
  intro t
  rfl

theorem map_id : map D D (ContinuousMonoidHom.id G) = ContinuousLinearMap.id ℝ (GleasonLieAlgebra D) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousMonoidHom.ext
  intro t
  rfl
end GleasonLieAlgebra
end DirectedCycles
