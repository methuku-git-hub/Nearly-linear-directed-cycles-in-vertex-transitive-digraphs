import DirectedCycles.CommutatorWords

set_option autoImplicit false
open scoped Pointwise commutatorElement
namespace DirectedCycles

theorem commutator_mem_power {G : Type*} [Group G] (A : Set G) (hAi : A⁻¹ = A)
    (a b : ℕ) {x y : G} (hx : x ∈ A^a) (hy : y ∈ A^b) :
    ⁅x,y⁆ ∈ A^(2*(a+b)) := by
  have hxi : x⁻¹ ∈ A^a := by
    have hh := Set.inv_mem_inv.mpr hx
    rwa [← inv_pow,hAi] at hh
  have hyi : y⁻¹ ∈ A^b := by
    have hh := Set.inv_mem_inv.mpr hy
    rwa [← inv_pow,hAi] at hh
  have hh := Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hx hy) hxi) hyi
  rw [← pow_add,← pow_add,← pow_add] at hh
  simpa only [commutatorElement_def,show a+b+a+b = 2*(a+b) by omega] using hh

private theorem commutator_cost_bound (a b M : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2*(4^a*M+4^b*M) ≤ 4^(a+b)*M := by
  have hpa : 4 ≤ 4^a := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) ha
  have hpb : 4 ≤ 4^b := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hb
  have hh : 2*(4^a+4^b) ≤ 4^a*4^b := by nlinarith
  have hm := Nat.mul_le_mul_right M hh
  rw [pow_add]
  nlinarith

theorem CommutatorWord.eval_mem_power {α G : Type*} [Group G]
    (w : CommutatorWord α) (x : α → G) (A : Set G) (h1 : 1 ∈ A) (hAi : A⁻¹ = A)
    (M : ℕ) (hx : ∀ i, x i ∈ A^M) : w.eval x ∈ A^(4^w.weight*M) := by
  induction w with
  | var i =>
    apply Set.pow_subset_pow_right h1 (show M ≤ 4^1*M by omega)
    exact hx i
  | bracket a b ha hb =>
    exact Set.pow_subset_pow_right h1 (commutator_cost_bound a.weight b.weight M a.weight_pos b.weight_pos)
      (commutator_mem_power A hAi _ _ ha hb)

theorem MarkedCommutatorWord.eval_mem_power {α G : Type*} [Group G]
    (w : MarkedCommutatorWord α) (h : G) (x : α → G)
    (A : Set G) (h1 : 1 ∈ A) (hAi : A⁻¹ = A)
    (M : ℕ) (hh : h ∈ A^M) (hx : ∀ i, x i ∈ A^M) :
    w.eval h x ∈ A^(4^(w.degree+1)*M) := by
  induction w with
  | marked =>
    exact Set.pow_subset_pow_right h1 (show M ≤ 4^(0+1)*M by omega) hh
  | left a b ha =>
    have hm := commutator_mem_power A hAi _ _ ha (b.eval_mem_power x A h1 hAi M hx)
    have hb := Set.pow_subset_pow_right h1
      (commutator_cost_bound (a.degree+1) b.weight M (by omega) b.weight_pos) hm
    simpa only [MarkedCommutatorWord.eval,MarkedCommutatorWord.degree,
      show a.degree+1+b.weight = a.degree+b.weight+1 by omega] using hb
  | right a b hb =>
    have hm := commutator_mem_power A hAi _ _ (a.eval_mem_power x A h1 hAi M hx) hb
    have ha := Set.pow_subset_pow_right h1
      (commutator_cost_bound a.weight (b.degree+1) M a.weight_pos (by omega)) hm
    simpa only [MarkedCommutatorWord.eval,MarkedCommutatorWord.degree,Nat.add_assoc] using ha

end DirectedCycles
