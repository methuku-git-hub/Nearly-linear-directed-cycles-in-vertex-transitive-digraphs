module

public import DirectedCycles.LocalOptimalEscapeBump
public import DirectedCycles.LocalPowerEscapeDerivativeBound
public import DirectedCycles.ScalarBootstrap

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

/-- The local Gleason bootstrap. The auxiliary infimum is restricted to
A-by-A multiplication nodes, precisely where derivative subadditivity has
been proved from the common support domain. -/
theorem gleason_bootstrap_core (hc : L.Cancellative) {A S R : Set G}
    (hA : L.one ∈ A) (hS : L.one ∈ S) (hAR : A ⊆ R) (hSR : S ⊆ R)
    (hdom : L.AllProductsDefined R 3)
    {ε C K M θ : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hθ : 0 ≤ θ) (hθhalf : θ ≤ 1/2)
    (f : G → ℝ) (hfR : ∀ x, f x ≠ 0 → x ∈ R) (hf : ‖f‖ ≤ K)
    (hescape : ∀ g, L.escapeNorm A g ≤ C*L.derivativeNorm f g)
    (htrap : ∀ g, L.escapeNorm S g ≤ M*L.escapeNorm A g)
    (hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g, L.derivativeNorm f g ≤ X*L.restrictedEscapeDistance A ε g)
    (hsecond : ∀ X : ℝ, 0 ≤ X →
      (∀ g, L.derivativeNorm f g ≤ X*L.restrictedEscapeDistance A ε g) →
      ∀ g ∈ A, ∀ h ∈ S, L.derivativeNorm (L.derivative g f) h ≤
        θ*X*L.restrictedEscapeDistance A ε g) :
    ∀ g, L.escapeNorm A g ≤ (8*C*K*M)*L.restrictedEscapeDistance A ε g := by
  let d := L.restrictedEscapeDistance A ε
  let B := 4*K*M
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hd : ∀ g, 0 ≤ d g := L.restrictedEscapeDistance_nonneg hA hε.le
  have hstep : ∀ X : ℝ, 0 ≤ X → (∀ g, L.derivativeNorm f g ≤ X*d g) →
      ∀ g, L.derivativeNorm f g ≤ (B+θ*X)*d g := by
    intro X hX hbound
    have hθX : 0 ≤ θ*X := mul_nonneg hθ hX
    have hpoint : ∀ g, L.derivativeNorm f g ≤ (B+θ*X)*(L.escapeNorm A g+ε) := by
      intro g
      have he0 := L.escapeNorm_nonneg hA g
      have hdle := L.restrictedEscapeDistance_le hA hε.le g
      have hmain : L.derivativeNorm f g ≤ B*L.escapeNorm A g+θ*X*d g := by
        by_cases hg : g ∈ A
        · have ht := L.derivativeNorm_le_escape_of_second hc hdom hSR (hAR hg) f hfR hS
            (mul_nonneg hθX (hd g)) (hsecond X hX hbound g hg)
          apply ht.trans
          apply add_le_add _ le_rfl
          calc
            4*‖f‖*L.escapeNorm S g ≤ 4*K*L.escapeNorm S g := by
              gcongr
              exact L.escapeNorm_nonneg hS g
            _ ≤ 4*K*(M*L.escapeNorm A g) := mul_le_mul_of_nonneg_left (htrap g) (by positivity)
            _ = B*L.escapeNorm A g := by dsimp [B]; ring
        · rw [L.escapeNorm_eq_one_of_not_mem hA hg]
          have ht := L.derivativeNorm_le_two_mul f g
          have hnonneg := mul_nonneg hθX (hd g)
          have hKM : K ≤ K*M := le_mul_of_one_le_right hK0.le hM
          dsimp [B]
          nlinarith
      have hterm : θ*X*d g ≤ θ*X*(L.escapeNorm A g+ε) := mul_le_mul_of_nonneg_left hdle hθX
      have hbase : B*L.escapeNorm A g ≤ B*(L.escapeNorm A g+ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hB.le
      nlinarith
    intro g
    have hcoef : 0 < B+θ*X := add_pos_of_pos_of_nonneg hB hθX
    exact L.le_mul_restrictedProductNorm hcoef
      (by simp only [derivativeNorm,L.derivative_one hc,norm_zero])
      (fun ha hb hm => L.derivativeNorm_mul_le hc hdom (hAR ha) (hAR hb) hm f hfR) hpoint g
  have hu := scalar_bootstrap_bound (L.derivativeNorm f) d hd hB.le hθ
    (by linarith : θ < 1) hstart hstep
  have hcoef : B/(1-θ) ≤ 2*B := by
    apply (div_le_iff₀ (by linarith : 0 < 1-θ)).2
    nlinarith
  intro g
  calc
    L.escapeNorm A g ≤ C*L.derivativeNorm f g := hescape g
    _ ≤ C*((B/(1-θ))*d g) := mul_le_mul_of_nonneg_left (hu g) hC
    _ ≤ C*((2*B)*d g) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef (hd g)) hC
    _ = (8*C*K*M)*L.restrictedEscapeDistance A ε g := by dsimp [B,d]; ring
end LocalGroupAlgebra
end DirectedCycles
