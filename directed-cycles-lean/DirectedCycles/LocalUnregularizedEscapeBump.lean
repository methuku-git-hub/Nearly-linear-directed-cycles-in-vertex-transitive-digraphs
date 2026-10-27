module

public import DirectedCycles.LocalOptimalEscapeBump

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem RestrictedProductCost.regularize {A : Set G} {w : G → ℝ} {g : G} {r : ℝ}
    (hp : L.RestrictedProductCost A w g r) :
    ∃ n : ℕ, ∀ ε : ℝ, L.RestrictedProductCost A (fun x => w x+ε) g (r+(n : ℝ)*ε) := by
  induction hp with
  | one => exact ⟨0,fun _ => by simpa using RestrictedProductCost.one⟩
  | leaf g => exact ⟨1,fun _ => by simpa using RestrictedProductCost.leaf (L := L) (A := A) g⟩
  | @mul a b c r s _ _ ha hb hm ih ih' =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,hm'⟩ := ih'
    refine ⟨n+m,fun ε => ?_⟩
    have hh := RestrictedProductCost.mul (hn ε) (hm' ε) ha hb hm
    convert hh using 1
    push_cast
    ring

/-- Uniform regularized bounds pass to the same restricted product norm
without regularization. Each finite cost tree has a finite number of leaves,
so its regularization error vanishes. -/
theorem escapeNorm_le_restricted_unregularized {A : Set G} {P : ℝ} (hP : 0 < P)
    (h : ∀ ε : ℝ, 0 < ε → ∀ g, L.escapeNorm A g ≤ P*L.restrictedEscapeDistance A ε g)
    (hA : L.one ∈ A) (g : G) :
    L.escapeNorm A g ≤ P*L.restrictedProductNorm A (L.escapeNorm A) g := by
  have hcost : ∀ r, L.RestrictedProductCost A (L.escapeNorm A) g r → L.escapeNorm A g ≤ P*r := by
    intro r hr
    obtain ⟨n,hn⟩ := hr.regularize L
    apply le_of_forall_pos_le_add
    intro η hη
    let t := P*(n : ℝ)+1
    have ht : 0 < t := by dsimp [t]; positivity
    let ε := η/t
    have hε : 0 < ε := div_pos hη ht
    have hb := (h ε hε g).trans (mul_le_mul_of_nonneg_left
      (L.restrictedProductNorm_le_cost (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε.le) (hn ε)) hP.le)
    have hte : t*ε = η := by dsimp [ε]; field_simp
    have herror : P*(n : ℝ)*ε ≤ η := by
      have hn' : P*(n : ℝ) ≤ t := by dsimp [t]; linarith
      exact (mul_le_mul_of_nonneg_right hn' hε.le).trans_eq hte
    nlinarith
  suffices hh : L.escapeNorm A g/P ≤ L.restrictedProductNorm A (L.escapeNorm A) g by
    simpa only [mul_comm] using (div_le_iff₀ hP).mp hh
  apply le_csInf (L.restrictedProductCost_nonempty A (L.escapeNorm A) g)
  intro r hr
  exact (div_le_iff₀ hP).2 (by simpa only [mul_comm] using hcost r hr)

/-- An actual unregularized local escape bump. Separation comes from the
uniform bootstrap rather than from an assumed metric or assumed bump. -/
theorem exists_unregularized_escape_bump [Fintype G]
    (hd : L.DivisionClosed) (hr : L.Reversible) (A : Finset G) (hA : L.one ∈ A)
    (hi : ∀ x ∈ A, L.inv x ∈ A) (hdom : L.AllProductsDefined (A : Set G) 3)
    {P : ℝ} (hP : 0 < P)
    (h : ∀ ε : ℝ, 0 < ε → ∀ g, L.escapeNorm A g ≤ P*L.restrictedEscapeDistance A ε g) :
    ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ A, φ x = 1) ∧ (∀ x, x ∉ L.wordPower (A : Set G) 2 → φ x = 0) ∧
      (∀ g x, |L.derivative g φ x| ≤ P*L.escapeNorm A g) := by
  have hw := L.escapeNorm_nonneg hA
  have hsep : ∀ g : G, g ∉ A → 1/P ≤ L.restrictedProductNorm (A : Set G) (L.escapeNorm A) g := by
    intro g hg
    have ht := L.escapeNorm_le_restricted_unregularized hP h hA g
    rw [L.escapeNorm_eq_one_of_not_mem hA hg] at ht
    exact (div_le_iff₀ hP).2 (by simpa only [mul_comm] using ht)
  obtain ⟨φ,hφ,hφA,hφs,hφlip⟩ := L.exists_factor_bump hd (hd.cancellative L hr)
    (L.restrictedProductNorm_nonneg hw) (L.restrictedProductNorm_one hw)
    (L.restrictedProductNorm_inv hr hi (L.escapeNorm_inv hr hi)) A
    (fun ha hb hm => L.restrictedProductNorm_mul_le hw ha hb hm) hA hi hdom
    (by positivity : 0 < 1/P) hsep
  refine ⟨φ,hφ,hφA,hφs,?_⟩
  intro g x
  apply (hφlip g x).trans
  simp only [one_div,div_inv_eq_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_weight hw g) hP.le
end LocalGroupAlgebra
end DirectedCycles
