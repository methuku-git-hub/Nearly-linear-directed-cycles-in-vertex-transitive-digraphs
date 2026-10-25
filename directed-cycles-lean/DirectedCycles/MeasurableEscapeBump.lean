module

public import DirectedCycles.OpenSetNormBump
public import DirectedCycles.RegularizedEscapeDistance

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G]

/-- A measurable regularized escape bump on an arbitrary open identity
window. A point within twice the true complement infimum replaces the
finite-case minimizer; no attainment hypothesis is added. -/
theorem measurable_optimal_escape_bump {A : Set G} (hA : (1 : G) ∈ A)
    (hAi : A⁻¹ = A) (hAo : IsOpen A) (hproper : ∃ b : G, b ∉ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∃ b : G, ε ≤ r ∧ b ∉ A ∧ regularizedEscapeDistance A ε b < 2*r ∧
      (∀ g : G, g ∉ A → r ≤ regularizedEscapeDistance A ε g) ∧
      ∃ φ : G → ℝ, Measurable φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x ∈ A, φ x = 1) ∧ (∀ x, x ∉ A^2 → φ x = 0) ∧
        (∀ g x, |φ (g⁻¹*x)-φ x| ≤ regularizedEscapeDistance A ε g/r) := by
  let d := regularizedEscapeDistance A ε
  let T := d '' Aᶜ
  have hT : T.Nonempty := by
    obtain ⟨b,hb⟩ := hproper
    exact ⟨d b,b,hb,rfl⟩
  have hεT : ∀ c ∈ T, ε ≤ c := by
    rintro c ⟨b,hb,rfl⟩
    exact le_regularizedEscapeDistance_of_not_mem hA hε.le hb
  have hTb : BddBelow T := ⟨ε,hεT⟩
  let r := sInf T
  have hrε : ε ≤ r := le_csInf hT hεT
  have hr : 0 < r := hε.trans_le hrε
  obtain ⟨c,⟨b,hb,rfl⟩,hbr⟩ := (csInf_lt_iff hTb hT).mp (by linarith : sInf T < 2*r)
  have hsep : ∀ g : G, g ∉ A → r ≤ d g := fun g hg => csInf_le hTb ⟨g,hg,rfl⟩
  let φ := openSetNormBump d A r
  have hd : ∀ g, 0 ≤ d g := regularizedEscapeDistance_nonneg hA hε.le
  refine ⟨r,b,hrε,hb,hbr,hsep,φ,openSetNormBump_measurable hd ⟨1,hA⟩ hAo r,
    openSetNormBump_bounds hd ⟨1,hA⟩ hr.le,?_,?_,?_⟩
  · intro x hx
    exact openSetNormBump_plateau hd (regularizedEscapeDistance_one hA hε.le) r hx
  · intro x hx
    exact openSetNormBump_support ⟨1,hA⟩ hr hsep hx
  · intro g x
    simpa only [φ,d,regularizedEscapeDistance_inv hAi ε] using openSetNormBump_lipschitz hd
      (regularizedEscapeDistance_mul_le hA hε.le) (regularizedEscapeDistance_inv hAi ε)
      ⟨1,hA⟩ hr g⁻¹ x
end DirectedCycles
