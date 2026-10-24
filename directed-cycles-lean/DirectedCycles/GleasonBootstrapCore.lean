import DirectedCycles.RegularizedEscapeDistance
import DirectedCycles.ScalarBootstrap
import DirectedCycles.PowerEscapeDerivativeBound

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [Fintype G]

/-- The complete analytic bootstrap once the two actual bumps supply its
explicit derivative estimates. All displayed hypotheses are ordinary lemma
inputs; the strong-group construction must supply every one of them. -/
theorem gleason_bootstrap_core {A S : Set G} (hA : 1 ∈ A) (hS : 1 ∈ S)
    {ε C K M θ : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hθ : 0 ≤ θ) (hθhalf : θ ≤ 1/2)
    (f : G → ℝ) (hf : ‖f‖ ≤ K)
    (hescape : ∀ g, escapeNorm A g ≤ C*derivativeNorm f g)
    (htrap : ∀ g, escapeNorm S g ≤ M*escapeNorm A g)
    (hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g,
      derivativeNorm f g ≤ X*regularizedEscapeDistance A ε g)
    (hsecond : ∀ X : ℝ, 0 ≤ X →
      (∀ g, derivativeNorm f g ≤ X*regularizedEscapeDistance A ε g) →
      ∀ g ∈ A, ∀ h ∈ S, derivativeNorm (groupDerivative g f) h ≤
        θ*X*regularizedEscapeDistance A ε g) :
    ∀ g, escapeNorm A g ≤ (8*C*K*M)*regularizedEscapeDistance A ε g := by
  let d := regularizedEscapeDistance A ε
  let B := 4*K*M
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hd : ∀ g, 0 ≤ d g := regularizedEscapeDistance_nonneg hA hε.le
  have hstep : ∀ X : ℝ, 0 ≤ X → (∀ g, derivativeNorm f g ≤ X*d g) →
      ∀ g, derivativeNorm f g ≤ (B+θ*X)*d g := by
    intro X hX hbound
    have hθX : 0 ≤ θ*X := mul_nonneg hθ hX
    have hpoint : ∀ g, derivativeNorm f g ≤ (B+θ*X)*(escapeNorm A g+ε) := by
      intro g
      have he0 := escapeNorm_nonneg hA g
      have hdle := regularizedEscapeDistance_le hA hε.le g
      have hmain : derivativeNorm f g ≤ B*escapeNorm A g + θ*X*d g := by
        by_cases hg : g ∈ A
        · have ht := derivativeNorm_le_escape_of_second f g hS
            (mul_nonneg hθX (hd g)) (hsecond X hX hbound g hg)
          apply ht.trans
          apply add_le_add _ le_rfl
          calc
            4*‖f‖*escapeNorm S g ≤ 4*K*escapeNorm S g := by
              gcongr
              exact escapeNorm_nonneg hS g
            _ ≤ 4*K*(M*escapeNorm A g) :=
              mul_le_mul_of_nonneg_left (htrap g) (by positivity)
            _ = B*escapeNorm A g := by dsimp [B]; ring
        · rw [escapeNorm_eq_one_of_not_mem hA hg]
          have ht := derivativeNorm_le_two_mul f g
          have hnonneg := mul_nonneg hθX (hd g)
          have hKM : K ≤ K*M := le_mul_of_one_le_right hK0.le hM
          dsimp [B]
          nlinarith
      have hterm : θ*X*d g ≤ θ*X*(escapeNorm A g+ε) :=
        mul_le_mul_of_nonneg_left hdle hθX
      have hbase : B*escapeNorm A g ≤ B*(escapeNorm A g+ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hB.le
      nlinarith
    intro g
    have hc : 0 < B+θ*X := add_pos_of_pos_of_nonneg hB hθX
    exact le_mul_wordNorm hc (by simp) (derivativeNorm_mul_le f) hpoint g
  have hu := scalar_bootstrap_bound (derivativeNorm f) d hd hB.le hθ
    (by linarith : θ < 1) hstart hstep
  have hcoef : B/(1-θ) ≤ 2*B := by
    apply (div_le_iff₀ (by linarith : 0 < 1-θ)).2
    nlinarith
  intro g
  calc
    escapeNorm A g ≤ C*derivativeNorm f g := hescape g
    _ ≤ C*((B/(1-θ))*d g) := mul_le_mul_of_nonneg_left (hu g) hC
    _ ≤ C*((2*B)*d g) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef (hd g)) hC
    _ = (8*C*K*M)*regularizedEscapeDistance A ε g := by dsimp [B,d]; ring
end DirectedCycles
