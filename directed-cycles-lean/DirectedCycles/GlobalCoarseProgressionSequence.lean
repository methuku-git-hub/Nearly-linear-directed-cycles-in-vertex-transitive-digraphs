module

public import DirectedCycles.GlobalStrongApproximateSequence
public import DirectedCycles.StrongFiniteSequenceNormalization
public import DirectedCycles.StrongFiniteProgressionSequence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Pointwise
namespace DirectedCycles

/-- The constructed strong finite subgroups, genuine NSS quotients, full
local induction and finite kernel restoration give a uniform progression
inside a fixed twentieth power. A final root-set reduction below sharpens
this fixed power to the fourth power required downstream. -/
theorem global_coarse_progression_sequence (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    ∃ r c J : ℕ, 1 ≤ J ∧ ∀ᶠ i in (u : Filter ℕ),
      ∃ P : CosetNilprogression (G i) r c,
        P.carrier ⊆ (A i : Set (G i))^20 ∧ (A i).card ≤ J*Nat.card P.carrier := by
  classical
  obtain ⟨L,J₀,hL,hJ₀,B,hBA,hgood⟩ := global_strong_approximate_sequence u hu G A K hK hA
  obtain ⟨B',hB',he⟩ := normalize_strong_finite_sequence (u : Filter ℕ) G B hL
    (hgood.mono fun _ hi => hi.1)
  obtain ⟨r,c,J₁,hJ₁,hP⟩ := strong_finite_progression_sequence u hu G B' L hL hB'
  refine ⟨r,c,J₀*J₁,by nlinarith,?_⟩
  filter_upwards [hP,hgood,he] with i hi hgi hei
  obtain ⟨P,hPA,hPc⟩ := hi
  rw [hei] at hPA hPc
  refine ⟨P,?_,?_⟩
  · exact hPA.trans (by simpa only [← pow_mul] using Set.pow_subset_pow_left (hBA i) (n := 5))
  · exact hgi.2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left J₀ hPc)
end DirectedCycles
