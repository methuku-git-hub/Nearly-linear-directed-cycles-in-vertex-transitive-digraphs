import DirectedCycles.CommutatorWordMultilinearity

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles

/-- The relative graded commutator takes values in a central subgroup. -/
theorem relative_commutator_image_central {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (i j : ℕ) :
    ∀ z ∈ ⁅relativeSeries N i,lowerSeries G j⁆,
      QuotientGroup.mk' (relativeSeries N (i+j+2)) z ∈
        Subgroup.center (G ⧸ relativeSeries N (i+j+2)) := by
  let q := QuotientGroup.mk' (relativeSeries N (i+j+2))
  have hc : (relativeSeries N (i+j+1)).map q ≤ Subgroup.center (G ⧸ relativeSeries N (i+j+2)) := by
    apply subgroup_image_central_of_commutator_le q (QuotientGroup.mk'_surjective _)
    rw [QuotientGroup.ker_mk']
    exact le_rfl
  intro z hz
  exact hc ⟨z,relative_lowerSeries_commutator_le N i j hz,rfl⟩

namespace MarkedCommutatorWord
variable {α : Type*}

def leafLabels : MarkedCommutatorWord α → List α
  | .marked => []
  | .left a b => a.leafLabels ++ b.leafLabels
  | .right a b => a.leafLabels ++ b.leafLabels

/-- Separate multiplicativity in the distinguished input modulo the next
relative level. No repetition condition on the other inputs is needed. -/
theorem eval_mul_marked_mod_next {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (w : MarkedCommutatorWord α)
    (x : α → G) (u v : G) (hu : u ∈ N) (hv : v ∈ N) :
    QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval (u*v) x) =
      QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval u x) *
      QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval v x) := by
  induction w with
  | marked => exact _root_.map_mul _ u v
  | left a b ha =>
    let A := relativeSeries N a.degree
    let B := lowerSeries G (b.weight-1)
    let K := relativeSeries N (a.degree+b.weight+1)
    let q := QuotientGroup.mk' K
    have hbpos := b.weight_pos
    have hc : ∀ z ∈ ⁅A,B⁆, q z ∈ Subgroup.center (G ⧸ K) := by
      have hh := relative_commutator_image_central N a.degree (b.weight-1)
      have he : a.degree+(b.weight-1)+2 = a.degree+b.weight+1 := by omega
      rw [he] at hh
      exact hh
    have herr : ⁅relativeSeries N (a.degree+1),B⁆ ≤ K := by
      have hh := relative_lowerSeries_commutator_le N (a.degree+1) (b.weight-1)
      have he : a.degree+1+(b.weight-1)+1 = a.degree+b.weight+1 := by omega
      rw [he] at hh
      exact hh
    have heq : QuotientGroup.mk' (relativeSeries N (a.degree+1)) (a.eval (u*v) x) =
        QuotientGroup.mk' (relativeSeries N (a.degree+1)) (a.eval u x*a.eval v x) := by
      rw [_root_.map_mul]
      exact ha
    have hcong := commutator_congr_left_mod (relativeSeries N (a.degree+1)) K B herr
      (b.eval_mem_lowerSeries x) heq
    exact hcong.trans (commutator_mul_left_mod q A B hc
      (a.eval_mem_relativeSeries N u hu x) (a.eval_mem_relativeSeries N v hv x)
      (b.eval_mem_lowerSeries x))
  | right a b hb =>
    let A := lowerSeries G (a.weight-1)
    let B := relativeSeries N b.degree
    let K := relativeSeries N (a.weight+b.degree+1)
    let q := QuotientGroup.mk' K
    have hapos := a.weight_pos
    have hc : ∀ z ∈ ⁅A,B⁆, q z ∈ Subgroup.center (G ⧸ K) := by
      have hh := relative_commutator_image_central N b.degree (a.weight-1)
      have he : b.degree+(a.weight-1)+2 = a.weight+b.degree+1 := by omega
      rw [Subgroup.commutator_comm]
      rw [he] at hh
      exact hh
    have herr : ⁅A,relativeSeries N (b.degree+1)⁆ ≤ K := by
      rw [Subgroup.commutator_comm]
      have hh := relative_lowerSeries_commutator_le N (b.degree+1) (a.weight-1)
      have he : b.degree+1+(a.weight-1)+1 = a.weight+b.degree+1 := by omega
      rw [he] at hh
      exact hh
    have heq : QuotientGroup.mk' (relativeSeries N (b.degree+1)) (b.eval (u*v) x) =
        QuotientGroup.mk' (relativeSeries N (b.degree+1)) (b.eval u x*b.eval v x) := by
      rw [_root_.map_mul]
      exact hb
    have hcong := commutator_congr_right_mod (relativeSeries N (b.degree+1)) K A herr
      (a.eval_mem_lowerSeries x) heq
    exact hcong.trans (commutator_mul_right_mod q A B hc (a.eval_mem_lowerSeries x)
      (b.eval_mem_relativeSeries N u hu x) (b.eval_mem_relativeSeries N v hv x))

end MarkedCommutatorWord
end DirectedCycles
