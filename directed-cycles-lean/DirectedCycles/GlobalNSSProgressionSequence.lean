import DirectedCycles.GlobalStrongApproximateSequence
import DirectedCycles.LocalLieProgressionInduction
import DirectedCycles.GlobalWindowProgressionTransfer
import DirectedCycles.GlobalWindowNSS
import DirectedCycles.LocalZeroDimensionalProgression

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Topology Manifold ContDiff Pointwise BigOperators
namespace DirectedCycles

/-- For finite approximate-group sequences whose fourth powers are NSS,
the constructed Lie model and complete local induction produce actual
uniformly dense global nilprogressions in those fourth powers. -/
theorem global_nss_progression_sequence (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i)))
    (hNSS : ∀ i, ∀ x : G i, (∀ n : ℕ, x^n ∈ (A i : Set (G i))^4) → x = 1) :
    ∃ r c J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ),
      ∃ P : CosetNilprogression (G i) r c,
        P.carrier ⊆ (A i : Set (G i))^4 ∧ (A i).card ≤ J*Nat.card P.carrier := by
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
  obtain ⟨L,J₁,_hL,hJ₁,B,hgood,⟨Nb⟩⟩ := N.exists_strong_submodel Y hQ C.source_division
    C.source_reversible (Filter.Eventually.of_forall C.source_one)
    (Filter.Eventually.of_forall C.source_inv) C.source_binary_domains
  have hnss : ∀ i, (C.windowAlgebra i).IsNSS (B i : Set (C.W i : Set (G i))) := by
    intro i
    have hh := global_window_nss (C.W i : Set (G i)) (C.W_data i).1 (C.W_data i).2.1 (by
      intro x hx
      apply hNSS i x
      intro n
      rw [← Finset.coe_pow]
      exact (C.W_data i).2.2 (hx n))
    exact fun S hS _hSB => hh S hS (Set.subset_univ _)
  have hp := local_lie_progression_induction (Module.finrank ℝ E) ℕ
    (fun i => (C.W i : Set (G i))) u C.windowAlgebra C.source_division C.source_reversible
    Q.carrier E (LocalGroupAlgebra.ofGroup Q.carrier) hQ
    (LocalGroupAlgebra.ofGroup_divisionClosed Q.carrier) (LocalGroupAlgebra.ofGroup_reversible Q.carrier)
    B L (hgood.mono fun _ hi => hi.2.2.approximate) (Filter.Eventually.of_forall hnss) Nb rfl
  obtain ⟨J₀,hJ₀,hcard⟩ := C.source_density
  have htotal : ∀ᶠ i in (u : Filter ℕ), (A i).card ≤ (J₀*J₁)*(B i).card := by
    filter_upwards [hcard,hgood] with i hi hgi
    exact hi.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J₀ hgi.2.1)
  have hp' := hp.of_containment_density (by nlinarith : 1 ≤ J₀*J₁)
    (Filter.Eventually.of_forall (fun i => Set.Subset.refl (B i : Set (C.W i : Set (G i))))) htotal
  have hg := hp'.globalWindowImage (fun i => (C.W i : Set (G i)))
    (fun i => (C.W_data i).1) (fun i => (C.W_data i).2.1)
  obtain ⟨r,c,J,hJ,_N,_hN,hW⟩ := hg
  refine ⟨r,c,J,hJ,?_⟩
  filter_upwards [hW] with i hi
  obtain ⟨W,_hW,hWcard⟩ := hi
  obtain ⟨P,hP,hPcard⟩ := global_progression_of_witness W (A i).card J hWcard
  refine ⟨P,?_,hPcard⟩
  intro x hx
  obtain ⟨y,_hy,rfl⟩ := hP hx
  rw [← Finset.coe_pow]
  exact (C.W_data i).2.2 y.property
end DirectedCycles
