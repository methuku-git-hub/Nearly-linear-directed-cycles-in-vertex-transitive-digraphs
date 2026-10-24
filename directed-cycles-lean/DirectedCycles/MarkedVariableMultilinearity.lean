import DirectedCycles.MarkedCommutatorMultilinearity

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles.MarkedCommutatorWord
variable {α : Type*}

theorem eval_one_marked {G : Type*} [Group G] (w : MarkedCommutatorWord α) (x : α → G) :
    w.eval 1 x = 1 := by
  induction w <;> simp_all [eval]

theorem eval_update_of_not_mem [DecidableEq α] {G : Type*} [Group G]
    (w : MarkedCommutatorWord α) (h : G) (x : α → G) (i : α) (v : G) (hi : i ∉ w.leafLabels) :
    w.eval h (Function.update x i v) = w.eval h x := by
  induction w with
  | marked => rfl
  | left a b ha =>
    have hab : i ∉ a.leafLabels ∧ i ∉ b.leafLabels := by simpa [leafLabels] using hi
    simp only [eval,ha hab.1,b.eval_update_of_not_mem x i v hab.2]
  | right a b hb =>
    have hab : i ∉ a.leafLabels ∧ i ∉ b.leafLabels := by simpa [leafLabels] using hi
    simp only [eval,hb hab.2,a.eval_update_of_not_mem x i v hab.1]

theorem eval_update_one_of_mem [DecidableEq α] {G : Type*} [Group G]
    (w : MarkedCommutatorWord α) (h : G) (x : α → G) (i : α) (hi : i ∈ w.leafLabels) :
    w.eval h (Function.update x i 1) = 1 := by
  induction w with
  | marked => simp [leafLabels] at hi
  | left a b ha =>
    rcases List.mem_append.mp hi with hi | hi
    · simp [eval,ha hi]
    · simp [eval,b.eval_update_one_of_mem x i hi]
  | right a b hb =>
    rcases List.mem_append.mp hi with hi | hi
    · simp [eval,a.eval_update_one_of_mem x i hi]
    · simp [eval,hb hi]

/-- Separate multiplicativity in every ordinary leaf modulo the next
relative central-series term. The marked input is constrained to N. -/
theorem eval_mul_variable_mod_next [DecidableEq α] {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (h : G) (hh : h ∈ N) (x : α → G)
    (i : α) (hi : i ∈ w.leafLabels) (u v : G) :
    QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval h (Function.update x i (u*v))) =
      QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval h (Function.update x i u)) *
      QuotientGroup.mk' (relativeSeries N (w.degree+1)) (w.eval h (Function.update x i v)) := by
  induction w with
  | marked => simp [leafLabels] at hi
  | left a b ha =>
    obtain ⟨hna,hnb,hdisj⟩ := List.nodup_append'.mp hw
    let A := relativeSeries N a.degree
    let B := lowerSeries G (b.weight-1)
    let K := relativeSeries N (a.degree+b.weight+1)
    let q := QuotientGroup.mk' K
    have hbpos := b.weight_pos
    have hc : ∀ z ∈ ⁅A,B⁆, q z ∈ Subgroup.center (G ⧸ K) := by
      have h := relative_commutator_image_central N a.degree (b.weight-1)
      have he : a.degree+(b.weight-1)+2 = a.degree+b.weight+1 := by omega
      rw [he] at h
      exact h
    rcases List.mem_append.mp hi with hia | hib
    · have hib : i ∉ b.leafLabels := List.disjoint_left.mp hdisj hia
      have herr : ⁅relativeSeries N (a.degree+1),B⁆ ≤ K := by
        have ht := relative_lowerSeries_commutator_le N (a.degree+1) (b.weight-1)
        have he : a.degree+1+(b.weight-1)+1 = a.degree+b.weight+1 := by omega
        rw [he] at ht
        exact ht
      have heq : QuotientGroup.mk' (relativeSeries N (a.degree+1)) (a.eval h (Function.update x i (u*v))) =
          QuotientGroup.mk' (relativeSeries N (a.degree+1))
            (a.eval h (Function.update x i u)*a.eval h (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact ha hna hia
      have hcong := commutator_congr_left_mod (relativeSeries N (a.degree+1)) K B herr
        (b.eval_mem_lowerSeries x) heq
      change q ⁅a.eval h (Function.update x i (u*v)),b.eval (Function.update x i (u*v))⁆ =
        q ⁅a.eval h (Function.update x i u),b.eval (Function.update x i u)⁆ *
        q ⁅a.eval h (Function.update x i v),b.eval (Function.update x i v)⁆
      rw [b.eval_update_of_not_mem x i (u*v) hib,b.eval_update_of_not_mem x i u hib,
        b.eval_update_of_not_mem x i v hib]
      exact hcong.trans (commutator_mul_left_mod q A B hc
        (a.eval_mem_relativeSeries N h hh _) (a.eval_mem_relativeSeries N h hh _)
        (b.eval_mem_lowerSeries x))
    · have hia : i ∉ a.leafLabels := List.disjoint_right.mp hdisj hib
      have herr : ⁅A,lowerSeries G b.weight⁆ ≤ K :=
        relative_lowerSeries_commutator_le N a.degree b.weight
      have heq : QuotientGroup.mk' (lowerSeries G b.weight) (b.eval (Function.update x i (u*v))) =
          QuotientGroup.mk' (lowerSeries G b.weight)
            (b.eval (Function.update x i u)*b.eval (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact b.eval_mul_mod_next hnb x i hib u v
      have hcong := commutator_congr_right_mod (lowerSeries G b.weight) K A herr
        (a.eval_mem_relativeSeries N h hh x) heq
      change q ⁅a.eval h (Function.update x i (u*v)),b.eval (Function.update x i (u*v))⁆ =
        q ⁅a.eval h (Function.update x i u),b.eval (Function.update x i u)⁆ *
        q ⁅a.eval h (Function.update x i v),b.eval (Function.update x i v)⁆
      rw [a.eval_update_of_not_mem h x i (u*v) hia,a.eval_update_of_not_mem h x i u hia,
        a.eval_update_of_not_mem h x i v hia]
      exact hcong.trans (commutator_mul_right_mod q A B hc
        (a.eval_mem_relativeSeries N h hh x) (b.eval_mem_lowerSeries _) (b.eval_mem_lowerSeries _))
  | right a b hb =>
    obtain ⟨hna,hnb,hdisj⟩ := List.nodup_append'.mp hw
    let A := lowerSeries G (a.weight-1)
    let B := relativeSeries N b.degree
    let K := relativeSeries N (a.weight+b.degree+1)
    let q := QuotientGroup.mk' K
    have hapos := a.weight_pos
    have hc : ∀ z ∈ ⁅A,B⁆, q z ∈ Subgroup.center (G ⧸ K) := by
      have ht := relative_commutator_image_central N b.degree (a.weight-1)
      have he : b.degree+(a.weight-1)+2 = a.weight+b.degree+1 := by omega
      rw [Subgroup.commutator_comm]
      rw [he] at ht
      exact ht
    rcases List.mem_append.mp hi with hia | hib
    · have hib : i ∉ b.leafLabels := List.disjoint_left.mp hdisj hia
      have herr : ⁅lowerSeries G a.weight,B⁆ ≤ K := by
        rw [Subgroup.commutator_comm]
        have ht := relative_lowerSeries_commutator_le N b.degree a.weight
        simpa only [Nat.add_comm b.degree a.weight] using ht
      have heq : QuotientGroup.mk' (lowerSeries G a.weight) (a.eval (Function.update x i (u*v))) =
          QuotientGroup.mk' (lowerSeries G a.weight)
            (a.eval (Function.update x i u)*a.eval (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact a.eval_mul_mod_next hna x i hia u v
      have hcong := commutator_congr_left_mod (lowerSeries G a.weight) K B herr
        (b.eval_mem_relativeSeries N h hh x) heq
      change q ⁅a.eval (Function.update x i (u*v)),b.eval h (Function.update x i (u*v))⁆ =
        q ⁅a.eval (Function.update x i u),b.eval h (Function.update x i u)⁆ *
        q ⁅a.eval (Function.update x i v),b.eval h (Function.update x i v)⁆
      rw [b.eval_update_of_not_mem h x i (u*v) hib,b.eval_update_of_not_mem h x i u hib,
        b.eval_update_of_not_mem h x i v hib]
      exact hcong.trans (commutator_mul_left_mod q A B hc
        (a.eval_mem_lowerSeries _) (a.eval_mem_lowerSeries _) (b.eval_mem_relativeSeries N h hh x))
    · have hia : i ∉ a.leafLabels := List.disjoint_right.mp hdisj hib
      have herr : ⁅A,relativeSeries N (b.degree+1)⁆ ≤ K := by
        rw [Subgroup.commutator_comm]
        have ht := relative_lowerSeries_commutator_le N (b.degree+1) (a.weight-1)
        have he : b.degree+1+(a.weight-1)+1 = a.weight+b.degree+1 := by omega
        rw [he] at ht
        exact ht
      have heq : QuotientGroup.mk' (relativeSeries N (b.degree+1)) (b.eval h (Function.update x i (u*v))) =
          QuotientGroup.mk' (relativeSeries N (b.degree+1))
            (b.eval h (Function.update x i u)*b.eval h (Function.update x i v)) := by
        rw [_root_.map_mul]
        exact hb hnb hib
      have hcong := commutator_congr_right_mod (relativeSeries N (b.degree+1)) K A herr
        (a.eval_mem_lowerSeries x) heq
      change q ⁅a.eval (Function.update x i (u*v)),b.eval h (Function.update x i (u*v))⁆ =
        q ⁅a.eval (Function.update x i u),b.eval h (Function.update x i u)⁆ *
        q ⁅a.eval (Function.update x i v),b.eval h (Function.update x i v)⁆
      rw [a.eval_update_of_not_mem x i (u*v) hia,a.eval_update_of_not_mem x i u hia,
        a.eval_update_of_not_mem x i v hia]
      exact hcong.trans (commutator_mul_right_mod q A B hc (a.eval_mem_lowerSeries x)
        (b.eval_mem_relativeSeries N h hh _) (b.eval_mem_relativeSeries N h hh _))

end DirectedCycles.MarkedCommutatorWord
