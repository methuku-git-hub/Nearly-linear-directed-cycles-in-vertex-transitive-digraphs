module

public import DirectedCycles.FiniteStructuralAlgebra
public import DirectedCycles.ApproximateSubgroupRestriction
public import DirectedCycles.FiniteConjugateBound

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The finite M=1 normal-envelope statement. Its proof is
finite_nilpotent_envelope in FiniteStructuralTheorems. -/
def FiniteNilpotentEnvelope : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∀ c : ℕ, ∃ C : ℕ, 1 ≤ C ∧
    ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
      Group.nilpotencyClass G ≤ c → ∀ A : Set G,
      IsApproximateSubgroup K A → Subgroup.closure A = ⊤ →
      ∀ H : Subgroup G, (H : Set G) ⊆ A →
        (Subgroup.normalClosure (H : Set G) : Set G) ⊆ A^C

/-- All finite-index and ambient-normality steps in TT 6.5, with the
nilpotent normal-envelope assertion isolated as the remaining premise. -/
theorem finite_envelope_of_nilpotent (hEnv : FiniteNilpotentEnvelope) : FiniteNormalEnvelope := by
  intro K hK c I
  let p := 2*I+2
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hKp : 1 ≤ K^(2*p-1) := one_le_pow₀ hK
  obtain ⟨C,hC,hEnv⟩ := hEnv (K^(2*p-1)) hKp c
  let D := I*(p*C)+2*I^2+1
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro G _ _ S hS1 _hSi hSgen N _ _ hc hI m hm happrox H hHN hHball
  let A := S^m
  have hAgen : Subgroup.closure A = ⊤ := by
    rw [Subgroup.closure_pow hS1 (by omega),hSgen]
  let B : Set N := N.subtype ⁻¹' (A^p)
  have hBgen : Subgroup.closure B = ⊤ := short_subgroup_preimage_generates A
    happrox.one_mem happrox.inv_eq_self hAgen N p (by dsimp [p]; omega)
  have hBapprox : IsApproximateSubgroup (K^(2*p-1)) B :=
    approximate_power_subgroup_preimage A K happrox N p hp
  let HN := H.subgroupOf N
  have hHNB : (HN : Set N) ⊆ B := by
    intro h hh
    exact Set.subset_pow happrox.one_mem (by omega : p ≠ 0) (hHball hh)
  let L := Subgroup.normalClosure (HN : Set N)
  have hLball : (L : Set N) ⊆ B^C := hEnv N hc B hBapprox hBgen HN hHNB
  let F := L.map N.subtype
  have hFN : F ≤ N := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := hg
    exact a.property
  have hnorm : N ≤ Subgroup.normalizer F := by
    have hh := Subgroup.le_normalizer_map (H := L) N.subtype
    have ht : Subgroup.normalizer (L : Set N) = ⊤ := (Subgroup.normalizer_eq_top_iff (H := L)).mpr inferInstance
    rw [ht,Subgroup.map_top,N.range_subtype] at hh
    exact hh
  have hFb : (F : Set G) ⊆ A^(p*C) := by
    rintro g ⟨a,ha,rfl⟩
    have hh : N.subtype a ∈ N.subtype '' (B^C) := ⟨a,hLball ha,rfl⟩
    rw [Set.image_pow,subtype_image_preimage] at hh
    have hh' := Set.pow_subset_pow_left (n := C) (Set.inter_subset_left : A^p ∩ (N : Set G) ⊆ A^p) hh
    simpa only [← pow_mul] using hh'
  have hHF : H ≤ F := by
    intro h hh
    exact ⟨⟨h,hHN hh⟩,Subgroup.subset_normalClosure hh,rfl⟩
  have hbound := finite_conjugate_normal_closure_bound A happrox.one_mem happrox.inv_eq_self
    hAgen N F hFN hnorm (p*C) hFb
  intro g hg
  have hh := hbound (Subgroup.normalClosure_mono hHF hg)
  have hexp : N.index*(p*C)+2*N.index^2 ≤ D := by
    dsimp [D]
    have h1 := Nat.mul_le_mul_right (p*C) hI
    have h2 := Nat.pow_le_pow_left hI 2
    omega
  have hh' := Set.pow_subset_pow_right happrox.one_mem hexp hh
  simpa only [A,← pow_mul,Nat.mul_comm m D] using hh'

end DirectedCycles
