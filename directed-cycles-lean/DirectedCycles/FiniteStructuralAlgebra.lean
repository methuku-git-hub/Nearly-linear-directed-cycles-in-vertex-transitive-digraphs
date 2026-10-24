import DirectedCycles.InducedStabilizerBound
import DirectedCycles.NilpotentQuotientImages
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Finite structural statement, proved by finite_approximate_structure
in FiniteStructuralTheorems. -/
def FiniteApproximateStructure : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ r c I n₀ : ℕ, 1 ≤ I ∧ 1 ≤ n₀ ∧
    ∀ (G : Type) [Group G] [Finite G] (S : Set G),
      1 ∈ S → S⁻¹ = S → Subgroup.closure S = ⊤ →
      ∀ m : ℕ, n₀ ≤ m → IsApproximateSubgroup K (S^m) →
      ∃ (H N : Subgroup G) (hH : H.Normal) (_hN : N.Normal),
        letI := hH
        H ≤ N ∧ (H : Set G) ⊆ S^(4*m) ∧
        ∃ _hNil : Group.IsNilpotent (N ⧸ H.comap N.subtype),
          Group.rank (N ⧸ H.comap N.subtype) ≤ r ∧
          Group.nilpotencyClass (N ⧸ H.comap N.subtype) ≤ c ∧ N.index ≤ I

/-- The finite normal-envelope assertion, proved by finite_normal_envelope;
all its quantitative bounds are uniform before the group is supplied. -/
def FiniteNormalEnvelope : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∀ c I : ℕ, ∃ C : ℕ, 1 ≤ C ∧
    ∀ (G : Type) [Group G] [Finite G] (S : Set G),
      1 ∈ S → S⁻¹ = S → Subgroup.closure S = ⊤ →
      ∀ (N : Subgroup G) [N.Normal] [Group.IsNilpotent N],
        Group.nilpotencyClass N ≤ c → N.index ≤ I →
        ∀ m : ℕ, 1 ≤ m → IsApproximateSubgroup K (S^m) →
        ∀ H : Subgroup G, H ≤ N → (H : Set G) ⊆ S^m →
          (Subgroup.normalClosure (H : Set G) : Set G) ⊆ S^(C*m)

/-- Pure algebra behind the finite structural conclusion: once a small
normal collapse is constructed, the actual induced group has all required
bounds. No metric containment or structure theorem is assumed implicitly. -/
theorem induced_structure_of_collapse {G V : Type*} [Group G] [Finite G] [Finite V]
    [MulAction G V] (N H L : Subgroup G) [N.Normal] [H.Normal] [L.Normal]
    [Group.IsNilpotent (N ⧸ H.comap N.subtype)] (hHL : H ≤ L) (hLN : L ≤ N)
    (hstab : ∀ x : V, N ⊓ MulAction.stabilizer G x ≤ L)
    (r c I : ℕ) (hr : Group.rank (N ⧸ H.comap N.subtype) ≤ r)
    (hc : Group.nilpotencyClass (N ⧸ H.comap N.subtype) ≤ c) (hI : N.index ≤ I) :
    letI := normalOrbitAction (V := V) L
    let Ω := Quotient (MulAction.orbitRel L V)
    let A := PermutationImage G Ω
    (∀ x : Ω, Nat.card (MulAction.stabilizer A x) ≤ I) ∧
    ∃ (M : Subgroup A) (_hM : M.Normal) (_hNil : Group.IsNilpotent M),
      Group.rank M ≤ r ∧ Group.nilpotencyClass M ≤ c ∧ M.index ≤ I := by
  let Ω := Quotient (MulAction.orbitRel L V)
  let : MulAction G Ω := normalOrbitAction L
  let f := normalOrbitImageHom (V := V) L
  let M := N.map f
  have hf : Function.Surjective f := normalOrbitImageHom_surjective L
  have hker : H ≤ f.ker := hHL.trans (subgroup_le_normalOrbitImage_kernel L)
  obtain ⟨hNil,hrM,hcM⟩ := nilpotent_image_quotient_bounds f N H hker
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  refine ⟨fun x => (induced_stabilizer_card_bound N L hLN hstab x).trans hI,
    M,inferInstance,hNil,hrM.trans hr,hcM.trans hc,?_⟩
  exact (Nat.le_of_dvd (show 0 < N.index by rw [Subgroup.index_eq_card]; exact Nat.card_pos)
    (N.index_map_dvd hf)).trans hI

end DirectedCycles
