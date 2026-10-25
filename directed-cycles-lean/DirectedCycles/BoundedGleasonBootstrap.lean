module

public import DirectedCycles.RegularizedEscapeDistance
public import DirectedCycles.ScalarBootstrap
public import DirectedCycles.BoundedDerivativeEscape

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]

/-- The analytic bootstrap on arbitrary groups, using actual bounded
translated differences and pointwise second derivatives. -/
theorem bounded_gleason_bootstrap_core {A S : Set G} (hA : 1 ∈ A) (hS : 1 ∈ S)
    {ε C K M θ : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hθ : 0 ≤ θ) (hθhalf : θ ≤ 1/2)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ K)
    (hescape : ∀ g, escapeNorm A g ≤ C*boundedDerivative f g)
    (htrap : ∀ g, escapeNorm S g ≤ M*escapeNorm A g)
    (hstart : ∃ X : ℝ, 0 ≤ X ∧ ∀ g,
      boundedDerivative f g ≤ X*regularizedEscapeDistance A ε g)
    (hsecond : ∀ X : ℝ, 0 ≤ X →
      (∀ g, boundedDerivative f g ≤ X*regularizedEscapeDistance A ε g) →
      ∀ g ∈ A, ∀ h ∈ S, ∀ x, |groupDerivative h (groupDerivative g f) x| ≤
        θ*X*regularizedEscapeDistance A ε g) :
    ∀ g, escapeNorm A g ≤ (8*C*K*M)*regularizedEscapeDistance A ε g := by
  let d := regularizedEscapeDistance A ε
  let B := 4*K*M
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hd : ∀ g, 0 ≤ d g := regularizedEscapeDistance_nonneg hA hε.le
  have hstep : ∀ X : ℝ, 0 ≤ X → (∀ g, boundedDerivative f g ≤ X*d g) →
      ∀ g, boundedDerivative f g ≤ (B+θ*X)*d g := by
    intro X hX hbound
    have hθX : 0 ≤ θ*X := mul_nonneg hθ hX
    have hpoint : ∀ g, boundedDerivative f g ≤ (B+θ*X)*(escapeNorm A g+ε) := by
      intro g
      have he0 := escapeNorm_nonneg hA g
      have hdle := regularizedEscapeDistance_le hA hε.le g
      have hmain : boundedDerivative f g ≤ B*escapeNorm A g + θ*X*d g := by
        by_cases hg : g ∈ A
        · have ht := boundedDerivative_le_escape_of_second hK0.le hf g hS
            (mul_nonneg hθX (hd g)) (hsecond X hX hbound g hg)
          apply ht.trans
          apply add_le_add _ le_rfl
          calc
            4*K*escapeNorm S g ≤ 4*K*(M*escapeNorm A g) :=
              mul_le_mul_of_nonneg_left (htrap g) (by positivity)
            _ = B*escapeNorm A g := by dsimp [B]; ring
        · rw [escapeNorm_eq_one_of_not_mem hA hg]
          have ht := boundedDerivative_le_two_bound hf g
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
    exact le_mul_wordNorm hc (by rw [boundedDerivative_one]) (boundedDerivative_mul_le hf) hpoint g
  have hu := scalar_bootstrap_bound (boundedDerivative f) d hd hB.le hθ
    (by linarith : θ < 1) hstart hstep
  have hcoef : B/(1-θ) ≤ 2*B := by
    apply (div_le_iff₀ (by linarith : 0 < 1-θ)).2
    nlinarith
  intro g
  calc
    escapeNorm A g ≤ C*boundedDerivative f g := hescape g
    _ ≤ C*((B/(1-θ))*d g) := mul_le_mul_of_nonneg_left (hu g) hC
    _ ≤ C*((2*B)*d g) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef (hd g)) hC
    _ = (8*C*K*M)*regularizedEscapeDistance A ε g := by dsimp [B,d]; ring
end DirectedCycles
