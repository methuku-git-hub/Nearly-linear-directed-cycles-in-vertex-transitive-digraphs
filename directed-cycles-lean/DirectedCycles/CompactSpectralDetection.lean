import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false
namespace DirectedCycles
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If a continuous linear map fails to fix the range of a compact
self-adjoint operator, that failure is already visible on a nonzero
eigenspace. The eigenspace is finite-dimensional by the spectral theorem. -/
theorem compact_spectral_detection [CompleteSpace E] (T R : E →L[𝕜] E)
    (hTc : IsCompactOperator T) (hTs : T.IsSymmetric) (hne : R.comp T ≠ T) :
    ∃ μ : 𝕜, μ ≠ 0 ∧ FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ) ∧
      ∃ v : E, v ∈ Module.End.eigenspace T.toLinearMap μ ∧ R v ≠ v := by
  classical
  by_contra hnot
  have hfix : ∀ μ : 𝕜, μ ≠ 0 → ∀ v : E,
      v ∈ Module.End.eigenspace T.toLinearMap μ → R v = v := by
    intro μ hμ v hv
    by_contra hn
    exact hnot ⟨μ,hμ,ContinuousLinearMap.finite_dimensional_eigenspace hTc μ hμ,v,hv,hn⟩
  let D : E →L[𝕜] E := R.comp T-T
  have hker : (⨆ μ : 𝕜, Module.End.eigenspace T.toLinearMap μ) ≤ D.ker := by
    apply iSup_le
    intro μ v hv
    have he : T v = μ • v := (Module.End.mem_eigenspace_iff).1 hv
    change R (T v)-T v = 0
    rw [he,map_smul]
    by_cases hμ : μ = 0
    · simp only [hμ,zero_smul,sub_self]
    · rw [hfix μ hμ v hv,sub_self]
  have hclosure : (⨆ μ : 𝕜, Module.End.eigenspace T.toLinearMap μ).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs)
  have htop : (⊤ : Submodule 𝕜 E) ≤ D.ker := by
    rw [← hclosure]
    exact Submodule.topologicalClosure_minimal _ hker D.isClosed_ker
  apply hne
  ext v
  have hz : D v = 0 := htop (Submodule.mem_top : v ∈ (⊤ : Submodule 𝕜 E))
  exact sub_eq_zero.mp hz

/-- Commutation preserves each actual eigenspace, allowing the finite
spectral witness to be used as an invariant representation space. -/
theorem commuting_operator_preserves_eigenspace (T R : E →L[𝕜] E)
    (hcomm : T.comp R = R.comp T) (μ : 𝕜) {v : E}
    (hv : v ∈ Module.End.eigenspace T.toLinearMap μ) :
    R v ∈ Module.End.eigenspace T.toLinearMap μ := by
  apply Module.End.mem_eigenspace_iff.2
  have h := congrArg (fun f : E →L[𝕜] E => f v) hcomm
  change T (R v) = R (T v) at h
  have hv' : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  change T (R v) = μ • R v
  rw [h,hv',map_smul]
end DirectedCycles
