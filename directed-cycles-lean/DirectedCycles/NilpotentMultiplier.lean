import DirectedCycles.NilpotentSpanning
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
namespace DirectedCycles

/-- The nilpotent multiplier argument modulo an invariant submodule. -/
theorem multiplier_mem_of_nilpotent_range {V : Type*} [AddCommGroup V]
    (N : Module.End ℤ V) (W : Submodule ℤ V) (m D : ℕ)
    (hW : W ≤ W.comap N) (hnil : N^D = 0)
    (hspan : ∀ v : V, m • v ∈ W ⊔ LinearMap.range N) :
    ∀ v : V, m^D • v ∈ W := by
  let QN := W.mapQ W N hW
  have hQN : QN^D = 0 := by
    change (W.mapQ W N hW)^D = 0
    rw [← W.mapQ_pow hW D]
    simp only [hnil,W.mapQ_zero]
  have hQR : ∀ x : V ⧸ W, ∃ y : V ⧸ W, m • x = QN y := by
    intro x
    obtain ⟨v,rfl⟩ := W.mkQ_surjective x
    obtain ⟨w,hw,z,hz,he⟩ := Submodule.mem_sup.mp (hspan v)
    obtain ⟨u,rfl⟩ := hz
    refine ⟨W.mkQ u,?_⟩
    change m • W.mkQ v = W.mkQ (N u)
    rw [← map_nsmul,← he,map_add]
    have hw0 : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
    rw [hw0,zero_add]
  intro v
  have h := exponent_of_nilpotent_range QN m D hQN hQR (W.mkQ v)
  rw [← map_nsmul] at h
  exact (Submodule.Quotient.mk_eq_zero W).mp h

/-- A quotient image containment is exactly containment modulo its kernel. -/
theorem multiplier_mem_sup_range {V : Type*} [AddCommGroup V]
    (N : Module.End ℤ V) (W : Submodule ℤ V) (m : ℕ)
    (h : ∀ v : V, m • (LinearMap.range N).mkQ v ∈ W.map (LinearMap.range N).mkQ) :
    ∀ v : V, m • v ∈ W ⊔ LinearMap.range N := by
  intro v
  have hv : m • v ∈ (W.map (LinearMap.range N).mkQ).comap (LinearMap.range N).mkQ := by
    change (LinearMap.range N).mkQ (m • v) ∈ W.map (LinearMap.range N).mkQ
    rw [map_nsmul]
    exact h v
  simpa only [Submodule.comap_map_eq,Submodule.ker_mkQ] using hv

end DirectedCycles
