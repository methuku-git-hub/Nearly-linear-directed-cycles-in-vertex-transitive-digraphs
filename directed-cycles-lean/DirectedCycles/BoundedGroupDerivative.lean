import DirectedCycles.PointwiseGroupDerivative
import DirectedCycles.EscapeNormTrapping

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- Supremum of actual translated differences on an arbitrary group. -/
noncomputable def boundedDerivative (f : G → ℝ) (g : G) : ℝ :=
  sSup (Set.range (fun x => |groupDerivative g f x|))

theorem groupDerivative_le_two_bound {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g x : G) : |groupDerivative g f x| ≤ 2*K := by
  change |f (g⁻¹*x)-f x| ≤ _
  exact (abs_sub _ _).trans ((add_le_add (hf _) (hf _)).trans_eq (by ring))

theorem boundedDerivative_bddAbove {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g : G) :
    BddAbove (Set.range (fun x => |groupDerivative g f x|)) :=
  ⟨2*K,by rintro _ ⟨x,rfl⟩; exact groupDerivative_le_two_bound hf g x⟩

theorem abs_groupDerivative_le_boundedDerivative {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g x : G) :
    |groupDerivative g f x| ≤ boundedDerivative f g :=
  le_csSup (boundedDerivative_bddAbove hf g) ⟨x,rfl⟩

theorem boundedDerivative_nonneg {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g : G) : 0 ≤ boundedDerivative f g :=
  (abs_nonneg _).trans (abs_groupDerivative_le_boundedDerivative hf g 1)

theorem boundedDerivative_le_iff {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g : G) (R : ℝ) :
    boundedDerivative f g ≤ R ↔ ∀ x, |groupDerivative g f x| ≤ R := by
  constructor
  · intro h x
    exact (abs_groupDerivative_le_boundedDerivative hf g x).trans h
  · intro h
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact h x)

theorem boundedDerivative_one (f : G → ℝ) : boundedDerivative f 1 = 0 := by
  simp [boundedDerivative]

theorem boundedDerivative_le_two_bound {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g : G) : boundedDerivative f g ≤ 2*K :=
  (boundedDerivative_le_iff hf g _).2 (groupDerivative_le_two_bound hf g)

theorem boundedDerivative_mul_le {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g h : G) :
    boundedDerivative f (g*h) ≤ boundedDerivative f g+boundedDerivative f h := by
  apply (boundedDerivative_le_iff hf _ _).2
  intro x
  rw [groupDerivative_mul]
  change |groupDerivative h f (g⁻¹*x)+groupDerivative g f x| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add
    (abs_groupDerivative_le_boundedDerivative hf h _)
    (abs_groupDerivative_le_boundedDerivative hf g _)).trans_eq (add_comm _ _))

theorem abs_pow_sub_one_le_boundedDerivative {f : G → ℝ} {K : ℝ}
    (hf : ∀ x, |f x| ≤ K) (g : G) (n : ℕ) :
    |f (g^n)-f 1| ≤ (n : ℝ)*boundedDerivative f g := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : |f (g^(n+1))-f (g^n)| ≤ boundedDerivative f g := by
      have h := abs_groupDerivative_le_boundedDerivative hf g (g^(n+1))
      simpa [groupDerivative,leftShift,pow_succ',abs_sub_comm] using h
    calc
      |f (g^(n+1))-f 1| ≤ |f (g^(n+1))-f (g^n)|+|f (g^n)-f 1| := abs_sub_le _ _ _
      _ ≤ boundedDerivative f g+(n : ℝ)*boundedDerivative f g := add_le_add hstep ih
      _ = ((n+1 : ℕ) : ℝ)*boundedDerivative f g := by push_cast; ring

/-- Escape is detected by the actual translated-difference supremum. -/
theorem escapeNorm_le_boundedDerivative {B : Set G} (hB : (1 : G) ∈ B)
    {f : G → ℝ} {K : ℝ} (hf : ∀ x, |f x| ≤ K)
    (hf1 : 1 ≤ f 1) (hfs : ∀ x, x ∉ B → f x = 0) (g : G) :
    escapeNorm B g ≤ boundedDerivative f g := by
  classical
  by_cases hex : ∃ n : ℕ, g^n ∉ B
  · let n := Nat.find hex
    have hn : g^n ∉ B := Nat.find_spec hex
    have hprev : ∀ i < n, g^i ∈ B := fun i hi => not_not.mp (Nat.find_min hex hi)
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      exact hn (by simpa [this] using hB)
    rw [escapeNorm_eq_inv_of_first_exit hB hn hprev]
    apply (div_le_iff₀ (by exact_mod_cast hn0 : 0 < (n : ℝ))).2
    have ht := abs_pow_sub_one_le_boundedDerivative hf g n
    rw [hfs _ hn,zero_sub,abs_neg,abs_of_nonneg (by linarith : 0 ≤ f 1)] at ht
    nlinarith
  · have hall : ∀ n : ℕ, g^n ∈ B := by simpa using hex
    rw [(escapeNorm_eq_zero_iff hB g).2 hall]
    exact boundedDerivative_nonneg hf g
end DirectedCycles
