import DirectedCycles.EscapeNormTrapping

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- An element cannot return to a region of very small escape norm between
its first escaping power N and power 2N. The argument uses division with a
short positive or negative remainder and the first trapping property. -/
theorem no_short_power_return {A : Set G} (hi : A⁻¹ = A) (C : ℕ)
    (htrap : ∀ x : G, (∀ j : ℕ, 1 ≤ j → j ≤ C → x^j ∈ A^2) → x ∈ A)
    (g : G) {N m : ℕ} (hN : 0 < N) (hNm : N ≤ m) (hmN : m < 2*N)
    (hexit : g^N ∉ A) (hprev : ∀ i < N, g^i ∈ A)
    (hreturn : ∀ j ≤ C+1, (g^m)^j ∈ A) : False := by
  have hm : 0 < m := hN.trans_le hNm
  apply hexit
  apply htrap
  intro k _ hk
  let t := k*N
  let q := t/m
  let r := t%m
  have hrm : r < m := Nat.mod_lt t hm
  have hqr : q*m+r = t := by dsimp [q,r]; exact Nat.div_add_mod' t m
  have hq : q ≤ C := by
    calc
      q ≤ (C*m)/m := Nat.div_le_div_right (by dsimp [t]; nlinarith)
      _ = C := Nat.mul_div_cancel C hm
  have ht : (g^N)^k = g^t := by dsimp [t]; rw [← pow_mul, Nat.mul_comm]
  rw [ht,pow_two]
  by_cases hrN : r < N
  · have hqm : g^(q*m) ∈ A := by simpa only [pow_mul, Nat.mul_comm] using hreturn q (by omega)
    have hgr := hprev r hrN
    refine ⟨g^(q*m),hqm,g^r,hgr,?_⟩
    change g^(q*m)*g^r = g^t
    rw [← pow_add,hqr]
  · have hmr : m-r < N := by omega
    have hpow : g^((q+1)*m) ∈ A := by
      simpa only [pow_mul, Nat.mul_comm] using hreturn (q+1) (by omega)
    have hrA := hprev (m-r) hmr
    have hrAi : (g^(m-r))⁻¹ ∈ A := by
      have h : (g^(m-r))⁻¹ ∈ A⁻¹ := Set.inv_mem_inv.mpr hrA
      simpa only [hi] using h
    have he : t+(m-r) = (q+1)*m := by
      have hsub := Nat.sub_add_cancel hrm.le
      nlinarith
    have hepow : g^((q+1)*m) = g^t*g^(m-r) := by rw [← pow_add,he]
    refine ⟨g^((q+1)*m),hpow,(g^(m-r))⁻¹,hrAi,?_⟩
    rw [hepow]
    simp
end DirectedCycles
