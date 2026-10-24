import DirectedCycles.StrongApproximateGroups

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The identity singleton satisfies both strong trapping tests with every
positive parameter. -/
theorem strong_finite_singleton {G : Type*} [Group G] {K : ℕ} (hK : 1 ≤ K) :
    IsStrongFiniteApproximateGroup K ({1} : Finset G) := by
  classical
  have ha : IsApproximateSubgroup (1 : ℝ) ({1} : Set G) :=
    @IsApproximateSubgroup.subgroup G _ (Subgroup G) _ _ ⊥
  have hQ : setConjugates ({1} : Set G) ({1} : Set G) = {1} := by
    ext x
    simp only [setConjugates,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨s,rfl,b,rfl,hx⟩
      simpa only [inv_one,mul_one] using hx
    · intro hx
      exact ⟨1,rfl,1,rfl,by simpa only [inv_one,mul_one] using hx⟩
  refine ⟨hK,by simpa only [Finset.coe_singleton] using ha.mono (by exact_mod_cast hK),{1},by simp,?_,?_,?_⟩
  · simp only [Finset.coe_singleton,Set.singleton_pow,one_pow,hQ,Set.Subset.refl]
  · intro x hx
    have hh := hx 1 (by omega) (by omega)
    simpa only [Finset.coe_singleton,Set.singleton_pow,one_pow,pow_one,Set.mem_singleton_iff,Finset.mem_singleton] using hh
  · intro x hx
    have hpos : 0 < 1000000*K^3 := Nat.mul_pos (by omega) (pow_pos (by omega) 3)
    have hh := hx 1 (by omega) (by omega)
    simpa only [pow_one,Finset.mem_singleton,Set.mem_singleton_iff] using hh

/-- Exceptional components can be replaced by the genuine identity
singleton, while all asserted eventual finite information is preserved. -/
theorem normalize_strong_finite_sequence {ι : Type*} (F : Filter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (A : ∀ i, Finset (G i)) {K : ℕ} (hK : 1 ≤ K)
    (hA : ∀ᶠ i in F, IsStrongFiniteApproximateGroup K (A i)) :
    ∃ B : ∀ i, Finset (G i), (∀ i, IsStrongFiniteApproximateGroup K (B i)) ∧
      ∀ᶠ i in F, B i = A i := by
  classical
  let B : ∀ i, Finset (G i) := fun i => if IsStrongFiniteApproximateGroup K (A i) then A i else {1}
  refine ⟨B,?_,?_⟩
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact hi
    · exact strong_finite_singleton hK
  · exact hA.mono fun i hi => by dsimp only [B]; rw [ite_eq_left hi]
end DirectedCycles
