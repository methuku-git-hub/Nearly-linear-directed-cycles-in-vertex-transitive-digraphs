module

public import DirectedCycles.CommutatorQuotients
public import DirectedCycles.CommutatorWords
public import DirectedCycles.GroupMultihom
public import Mathlib.Data.List.Nodup

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles
namespace CommutatorWord
variable {α : Type*}

def leafLabels : CommutatorWord α → List α
  | .var i => [i]
  | .bracket a b => a.leafLabels ++ b.leafLabels

theorem eval_update_of_not_mem [DecidableEq α] {G : Type*} [Group G]
    (w : CommutatorWord α) (x : α → G) (i : α) (v : G) (hi : i ∉ w.leafLabels) :
    w.eval (Function.update x i v) = w.eval x := by
  induction w with
  | var j =>
    have hj : j ≠ i := by intro he; subst j; exact hi (by simp [leafLabels])
    simp [eval,hj]
  | bracket a b ha hb =>
    have hab : i ∉ a.leafLabels ∧ i ∉ b.leafLabels := by simpa [leafLabels] using hi
    simp only [eval,ha hab.1,hb hab.2]

theorem eval_update_one_of_mem [DecidableEq α] {G : Type*} [Group G]
    (w : CommutatorWord α) (x : α → G) (i : α) (hi : i ∈ w.leafLabels) :
    w.eval (Function.update x i 1) = 1 := by
  induction w with
  | var j =>
    have he : i = j := by simpa [leafLabels] using hi
    subst j
    simp [eval]
  | bracket a b ha hb =>
    rcases List.mem_append.mp hi with hi | hi
    · simp [eval,ha hi]
    · simp [eval,hb hi]

/-- A commutator form is separately multiplicative in each leaf modulo the
next lower-central level. Distinct leaf labels are essential. -/
theorem eval_mul_mod_next [DecidableEq α] {G : Type*} [Group G]
    (w : CommutatorWord α) (hw : w.leafLabels.Nodup) (x : α → G)
    (i : α) (hi : i ∈ w.leafLabels) (u v : G) :
    QuotientGroup.mk' (lowerSeries G w.weight) (w.eval (Function.update x i (u*v))) =
      QuotientGroup.mk' (lowerSeries G w.weight) (w.eval (Function.update x i u)) *
      QuotientGroup.mk' (lowerSeries G w.weight) (w.eval (Function.update x i v)) := by
  induction w with
  | var j =>
    have he : i = j := by simpa [leafLabels] using hi
    subst j
    simp [eval]
  | bracket a b ha hb =>
    obtain ⟨hna,hnb,hdisj⟩ := List.nodup_append'.mp hw
    let n := a.weight+b.weight
    let A := lowerSeries G (a.weight-1)
    let B := lowerSeries G (b.weight-1)
    let N := lowerSeries G n
    let q := QuotientGroup.mk' N
    have hapos := a.weight_pos
    have hbpos := b.weight_pos
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hc0 : ⁅A,B⁆ ≤ lowerSeries G (n-1) := by
      have hh := lowerSeries_commutator_le (G := G) (a.weight-1) (b.weight-1)
      have he : a.weight-1+(b.weight-1)+1 = n-1 := by dsimp [n]; omega
      simpa only [A,B,he] using hh
    have hnext : ⁅lowerSeries G (n-1),(⊤ : Subgroup G)⁆ ≤ q.ker := by
      rw [QuotientGroup.ker_mk']
      change lowerSeries G ((n-1)+1) ≤ lowerSeries G n
      rw [Nat.sub_add_cancel hn]
    have hc : ∀ z ∈ ⁅A,B⁆, q z ∈ Subgroup.center (G ⧸ N) := by
      intro z hz
      exact subgroup_image_central_of_commutator_le q (QuotientGroup.mk'_surjective N)
        (lowerSeries G (n-1)) hnext ⟨z,hc0 hz,rfl⟩
    rcases List.mem_append.mp hi with hia | hib
    · have hib : i ∉ b.leafLabels := List.disjoint_left.mp hdisj hia
      have herr : ⁅lowerSeries G a.weight,B⁆ ≤ N := by
        have hh := lowerSeries_commutator_le (G := G) a.weight (b.weight-1)
        have he : a.weight+(b.weight-1)+1 = n := by dsimp [n]; omega
        simpa only [B,N,he] using hh
      have hchild := ha hna hia
      have heq : QuotientGroup.mk' (lowerSeries G a.weight) (a.eval (Function.update x i (u*v))) =
          QuotientGroup.mk' (lowerSeries G a.weight)
            (a.eval (Function.update x i u)*a.eval (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact hchild
      have hcong := commutator_congr_left_mod (lowerSeries G a.weight) N B herr
        (b.eval_mem_lowerSeries x) heq
      change q ⁅a.eval (Function.update x i (u*v)),b.eval (Function.update x i (u*v))⁆ =
        q ⁅a.eval (Function.update x i u),b.eval (Function.update x i u)⁆ *
        q ⁅a.eval (Function.update x i v),b.eval (Function.update x i v)⁆
      rw [b.eval_update_of_not_mem x i (u*v) hib,b.eval_update_of_not_mem x i u hib,
        b.eval_update_of_not_mem x i v hib]
      exact hcong.trans (commutator_mul_left_mod q A B hc
        (a.eval_mem_lowerSeries _) (a.eval_mem_lowerSeries _) (b.eval_mem_lowerSeries x))
    · have hia : i ∉ a.leafLabels := List.disjoint_right.mp hdisj hib
      have herr : ⁅A,lowerSeries G b.weight⁆ ≤ N := by
        have hh := lowerSeries_commutator_le (G := G) (a.weight-1) b.weight
        have he : a.weight-1+b.weight+1 = n := by dsimp [n]; omega
        simpa only [A,N,he] using hh
      have hchild := hb hnb hib
      have heq : QuotientGroup.mk' (lowerSeries G b.weight) (b.eval (Function.update x i (u*v))) =
          QuotientGroup.mk' (lowerSeries G b.weight)
            (b.eval (Function.update x i u)*b.eval (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact hchild
      have hcong := commutator_congr_right_mod (lowerSeries G b.weight) N A herr
        (a.eval_mem_lowerSeries x) heq
      change q ⁅a.eval (Function.update x i (u*v)),b.eval (Function.update x i (u*v))⁆ =
        q ⁅a.eval (Function.update x i u),b.eval (Function.update x i u)⁆ *
        q ⁅a.eval (Function.update x i v),b.eval (Function.update x i v)⁆
      rw [a.eval_update_of_not_mem x i (u*v) hia,a.eval_update_of_not_mem x i u hia,
        a.eval_update_of_not_mem x i v hia]
      exact hcong.trans (commutator_mul_right_mod q A B hc
        (a.eval_mem_lowerSeries x) (b.eval_mem_lowerSeries _) (b.eval_mem_lowerSeries _))

end CommutatorWord
end DirectedCycles
