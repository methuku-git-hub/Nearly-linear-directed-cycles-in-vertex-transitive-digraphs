import DirectedCycles.GlobalKernelWindowSourceData
import DirectedCycles.GlobalLieLocalSmoothness
import DirectedCycles.LocalSmoothModelStrongSubmodel
import DirectedCycles.StrongGlobalWindowTransfer

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology Manifold ContDiff Pointwise
namespace DirectedCycles

/-- Actual finite approximate-group sequences contain uniformly dense
strong finite approximate groups in their fourth powers. The Lie model,
finite domain windows and strong trapping tests are all constructed. -/
theorem global_strong_approximate_sequence (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    ∃ L J : ℕ, 1 ≤ L ∧ 1 ≤ J ∧ ∃ B : ∀ i, Finset (G i),
      (∀ i, (B i : Set (G i)) ⊆ (A i : Set (G i))^4) ∧
      ∀ᶠ i in (u : Filter ℕ), IsStrongFiniteApproximateGroup L (B i) ∧
        (A i).card ≤ J*(B i).card := by
  classical
  obtain ⟨M,⟨D⟩⟩ := exists_global_good_lie_quotient u hu G A K hK hA
  obtain ⟨C⟩ := global_good_model_kernel_windows u G A (fun i => (hA i).one_mem) M D
  obtain ⟨N⟩ := C.exists_local_model
  let Q := lieQuotientGoodModel M D
  let E := EuclideanSpace ℝ (Fin D.dimension)
  let : ChartedSpace E Q.carrier := D.charts
  let : LieGroup 𝓘(ℝ,E) ∞ Q.carrier := lieQuotientGoodModel_lie M D
  let : ∀ i, Fintype (C.W i : Set (G i)) := fun i => Fintype.ofFinite _
  have hQ : LocalGroupSmoothness (E := E) (LocalGroupAlgebra.ofGroup Q.carrier) :=
    global_lie_local_smoothness
  obtain ⟨Y⟩ := smooth_local_exponential_data (LocalGroupAlgebra.ofGroup Q.carrier) hQ
  obtain ⟨L,J₁,hL,hJ₁,B',hgood,_hmodel⟩ := N.exists_strong_submodel Y hQ C.source_division
    C.source_reversible (Filter.Eventually.of_forall C.source_one)
    (Filter.Eventually.of_forall C.source_inv) C.source_binary_domains
  obtain ⟨J₀,hJ₀,hcard⟩ := C.source_density
  let B : ∀ i, Finset (G i) := fun i => (B' i).image Subtype.val
  refine ⟨L,J₀*J₁,hL,by nlinarith,B,?_,?_⟩
  · intro i x hx
    obtain ⟨y,_hy,rfl⟩ := Finset.mem_image.mp hx
    have hy : y.val ∈ (C.W i : Set (G i)) := y.property
    have hh := (C.W_data i).2.2 hy
    rw [← Finset.coe_pow]
    exact hh
  · filter_upwards [hgood,hcard] with i hi hci
    have hstrong := strong_global_window_transfer (C.W i : Set (G i))
      (C.W_data i).1 (C.W_data i).2.1 hi.2.2
    refine ⟨hstrong,?_⟩
    have he : (B i).card = (B' i).card := Finset.card_image_of_injective _ Subtype.val_injective
    rw [he]
    exact hci.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J₀ hi.2.1)
end DirectedCycles
