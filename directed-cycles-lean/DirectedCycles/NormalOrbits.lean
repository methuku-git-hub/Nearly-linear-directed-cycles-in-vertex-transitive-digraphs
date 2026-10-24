import DirectedCycles.Averaging
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false
namespace DirectedCycles

/-- Normality preserves the orbit equivalence relation under the ambient action. -/
theorem normal_orbitRel_invariant {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] (g : G) (x y : V) :
    MulAction.orbitRel H V (g • x) (g • y) ↔ MulAction.orbitRel H V x y := by
  have forward : ∀ (a : G) (u v : V), MulAction.orbitRel H V u v →
      MulAction.orbitRel H V (a • u) (a • v) := by
    intro a u v huv
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp huv
    change h.val • v = u at hh
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨a * h.val * a⁻¹, Subgroup.Normal.conj_mem inferInstance h.val h.property a⟩, ?_⟩
    change (a * h.val * a⁻¹) • (a • v) = a • u
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun z => a • z) hh
  constructor
  · intro h
    simpa only [inv_smul_smul] using forward g⁻¹ (g • x) (g • y) h
  · exact forward g x y

/-- A normal-orbit projection is an invariant partition. -/
theorem normal_orbit_projection_invariant {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) [H.Normal] (g : G) (x y : V) :
    (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel H V)) = Quotient.mk'' (g • y) ↔
    (Quotient.mk'' x : Quotient (MulAction.orbitRel H V)) = Quotient.mk'' y := by
  rw [Quotient.eq'', Quotient.eq'']
  exact normal_orbitRel_invariant H g x y

end DirectedCycles
