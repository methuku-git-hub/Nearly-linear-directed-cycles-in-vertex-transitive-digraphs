import DirectedCycles.LocalConjugateTransfer
import DirectedCycles.LocalPowerTrappingReflection
import DirectedCycles.LocalApproximateFiniteTransfer
import DirectedCycles.StrongLocalApproximateGroups

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Strong trapping of actual internal source sets gives genuine strong
finite approximate groups, including all long conjugate-word domains. -/
theorem localStrongFiniteApproximate_eventually {K : ℕ}
    (A : ∀ i, Finset (G i)) (S : ∀ i, Set (G i))
    (hA : IsLocalApproximateSet (localUltraAlgebra (U : Filter ι) G L) K
      (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))))
    (hSi : ∀ s ∈ localUltraSet (U : Filter ι) G S,
      (localUltraAlgebra (U : Filter ι) G L).inv s ∈ localUltraSet (U : Filter ι) G S)
    (hQdom : (localUltraAlgebra (U : Filter ι) G L).AllProductsDefined
      ((localUltraAlgebra (U : Filter ι) G L).conjugates (localUltraSet (U : Filter ι) G S)
        ((localUltraAlgebra (U : Filter ι) G L).wordPower
          (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) 4)) (1000*K^3))
    (hQA : (localUltraAlgebra (U : Filter ι) G L).wordPower
      ((localUltraAlgebra (U : Filter ι) G L).conjugates (localUltraSet (U : Filter ι) G S)
        ((localUltraAlgebra (U : Filter ι) G L).wordPower
          (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) 4)) (1000*K^3)
        ⊆ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hfirst : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000 →
      (localUltraAlgebra (U : Filter ι) G L).PowerIn
        ((localUltraAlgebra (U : Filter ι) G L).wordPower
          (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) 100) x j) →
        x ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (hsecond : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ 1000000*K^3 →
      (localUltraAlgebra (U : Filter ι) G L).PowerIn
        (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) x j) →
        x ∈ localUltraSet (U : Filter ι) G S) :
    ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i) := by
  let Q := fun i => (L i).conjugates (S i) ((L i).wordPower (A i : Set (G i)) 4)
  have hQeq : (localUltraAlgebra (U : Filter ι) G L).conjugates (localUltraSet (U : Filter ι) G S)
      ((localUltraAlgebra (U : Filter ι) G L).wordPower
        (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))) 4) =
      localUltraSet (U : Filter ι) G Q := by
    rw [localUltra_wordPower U G L,localUltra_conjugates U G L]
  rw [hQeq] at hQdom hQA
  have hdom := (localUltra_allProductsDefined_iff U G L Q (1000*K^3)).1 hQdom
  have hsmall : ∀ᶠ i in (U : Filter ι), (L i).wordPower (Q i) (1000*K^3) ⊆ (A i : Set (G i)) := by
    apply (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ _).1
    rwa [localUltra_wordPower U G L] at hQA
  have h₁ := localUltra_power_trapping_eventually U G L (fun i => (A i : Set (G i)))
    (fun i => (L i).wordPower (A i : Set (G i)) 100) 1000
    (by simpa only [localUltra_wordPower U G L] using hfirst)
  have h₂ := localUltra_power_trapping_eventually U G L S (fun i => (A i : Set (G i)))
    (1000000*K^3) hsecond
  filter_upwards [localFiniteApproximate_eventually U G L A hA,
    (localUltra_inv_closed_iff U G L S).1 hSi,hdom,hsmall,h₁,h₂] with i hi hsi hdi hsmalli h₁i h₂i
  exact ⟨hi,⟨S i,hsi,hdi,hsmalli,h₁i,h₂i⟩⟩
end DirectedCycles
