module

public import DirectedCycles.LocalEscapeTrapping
public import DirectedCycles.LocalPowerExtension
public import DirectedCycles.LocalTaylorEstimate
public import DirectedCycles.LocalUltraproductEscape

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- Telescoping follows actual successive products of a finite power segment;
no product outside that segment is used. -/
theorem abs_powerSegment_sub_one_le (hc : L.Cancellative) (f : G → ℝ)
    {g : G} {N : ℕ} (p : L.PowerSegment g N) {n : ℕ} (hn : n ≤ N) :
    |f (p.power n)-f L.one| ≤ (n : ℝ)*L.derivativeNorm f g := by
  induction n with
  | zero => simp only [p.zero,sub_self,abs_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    have hm : L.mulRel g (p.power n) (p.power (n+1)) := by
      have hp := p.add (n := 1) (m := n) (by omega)
      simpa only [p.one (by omega : 1 ≤ N),Nat.add_comm] using hp
    have hstep : |f (p.power (n+1))-f (p.power n)| ≤ L.derivativeNorm f g := by
      have hh := L.abs_derivative_le f g (p.power (n+1))
      simpa only [derivative,Pi.sub_apply,L.leftShift_of_mulRel hc hm,abs_sub_comm] using hh
    calc
      |f (p.power (n+1))-f L.one| ≤
          |f (p.power (n+1))-f (p.power n)| + |f (p.power n)-f L.one| := abs_sub_le _ _ _
      _ ≤ L.derivativeNorm f g+(n : ℝ)*L.derivativeNorm f g := add_le_add hstep (ih (by omega))
      _ = ((n+1 : ℕ) : ℝ)*L.derivativeNorm f g := by push_cast; ring

/-- The first failure of staying in B has an actual product value, because
binary products on B extend the preceding finite segment. Telescoping that
segment gives the local bump-to-escape estimate. -/
theorem escapeNorm_le_derivativeNorm (hc : L.Cancellative) {B : Set G}
    (hB1 : L.one ∈ B) (hB : ∀ x ∈ B, ∀ y ∈ B, L.Defined x y)
    (f : G → ℝ) (hf1 : 1 ≤ f L.one) (hfs : ∀ x, x ∉ B → f x = 0) (g : G) :
    L.escapeNorm B g ≤ L.derivativeNorm f g := by
  classical
  by_cases hg : g ∈ B
  · by_cases hex : ∃ n : ℕ, ¬ L.PowerIn B g n
    · let n := Nat.find hex
      have hbad : ¬ L.PowerIn B g n := Nat.find_spec hex
      have hprev : ∀ i < n, L.PowerIn B g i := fun i hi => not_not.mp (Nat.find_min hex hi)
      have hnpos : 0 < n := by
        by_contra hn
        have he : n = 0 := by omega
        exact hbad (he ▸ (L.powerIn_zero B g).2 hB1)
      have hshort : ∀ i ≤ n-1, L.PowerIn B g i := fun i hi => hprev i (by omega)
      let p := L.powerSegmentOfPowerIn hshort
      obtain ⟨z,hz⟩ := p.extend_product L
        (fun i hi => L.powerSegmentOfPowerIn_mem hshort hi) hg hB
      have hn : n-1+1 = n := by omega
      rw [hn] at hz
      have hzB : z ∉ B := fun hm => hbad ⟨z,hm,hz⟩
      have hall : ∀ i ≤ n, L.PowerIn (Set.univ : Set G) g i := by
        intro i hi
        by_cases hei : i = n
        · subst i
          exact ⟨z,Set.mem_univ _,hz⟩
        · obtain ⟨v,_,hv⟩ := hprev i (by omega)
          exact ⟨v,Set.mem_univ _,hv⟩
      let q := L.powerSegmentOfPowerIn hall
      have hqz : q.power n = z := (q.product n le_rfl).unique L hz
      have ht := L.abs_powerSegment_sub_one_le hc f q le_rfl
      rw [hqz,hfs z hzB,zero_sub,abs_neg,abs_of_nonneg (by linarith : 0 ≤ f L.one)] at ht
      rw [L.escapeNorm_eq_inv_of_first_exit hB1 hbad hprev]
      apply (div_le_iff₀ (by exact_mod_cast hnpos : 0 < (n : ℝ))).2
      nlinarith
    · have hall : ∀ n : ℕ, L.PowerIn B g n := by simpa only [not_exists,not_not] using hex
      rw [(L.escapeNorm_eq_zero_iff hB1 g).2 hall]
      exact L.derivativeNorm_nonneg f g
  · rw [L.escapeNorm_eq_one_of_not_mem hB1 hg]
    have hh := L.abs_derivative_le f g g
    have hnonneg : 0 ≤ f L.one := by linarith
    simp only [derivative,Pi.sub_apply,L.leftShift_of_mulRel hc (L.mul_one g),
      hfs g hg,sub_zero,abs_of_nonneg hnonneg] at hh
    exact hf1.trans hh

/-- The local BGT trapping and telescoping estimate with its explicit
constant. The only domain premise is binary multiplication on the bump's
support set, which bounded word domains supply in the applications. -/
theorem escapeNorm_le_mul_derivativeNorm (hc : L.Cancellative) {A B : Set G}
    (hB1 : L.one ∈ B) (hB : ∀ x ∈ B, ∀ y ∈ B, L.Defined x y)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn B x j) → x ∈ A)
    (f : G → ℝ) (hf1 : 1 ≤ f L.one) (hfs : ∀ x, x ∉ B → f x = 0) (g : G) :
    L.escapeNorm A g ≤ (C : ℝ)*L.derivativeNorm f g :=
  (L.escapeNorm_le_mul_of_trapping hB1 C hC htrap g).trans
    (mul_le_mul_of_nonneg_left (L.escapeNorm_le_derivativeNorm hc hB1 hB f hf1 hfs g)
      (Nat.cast_nonneg C))
end LocalGroupAlgebra
end DirectedCycles
