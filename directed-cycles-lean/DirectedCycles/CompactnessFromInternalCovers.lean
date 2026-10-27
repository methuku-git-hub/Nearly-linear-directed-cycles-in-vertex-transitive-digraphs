module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise Topology
namespace DirectedCycles

/-- A compactness criterion proved from finite translate covers and an
explicit countable intersection property. It does not assume compactness,
completeness, metrizability or a Lie model. -/
theorem compact_of_finite_covers_and_saturation {G : Type*} [Group G] [TopologicalSpace G]
    (T : Set G) (S : ℕ → Set G)
    (hbasis : ∀ x : G, (𝓝 x).HasBasis (fun _ : ℕ => True) (fun n => (fun y => x*y) '' S n))
    (hinv : ∀ n, (S n)⁻¹ = S n) (hsq : ∀ n, (S (n+1))^2 ⊆ S n)
    (hcover : ∀ n, ∃ F : Finset G, T ⊆ ⋃ x ∈ F, (fun y => x*y) '' S n)
    (hsat : ∀ c : ℕ → G,
      (∀ N, ∃ z ∈ T, ∀ n ≤ N, z ∈ (fun y => c n*y) '' S n) →
      ∃ z ∈ T, ∀ n, z ∈ (fun y => c n*y) '' S n) : IsCompact T := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro v hvT
  have hchoose : ∀ n, ∃ c : G, (fun y => c*y) '' S n ∈ (v : Filter G) := by
    intro n
    obtain ⟨F,hF⟩ := hcover n
    have hh : (⋃ x ∈ F, (fun y => x*y) '' S n) ∈ (v : Filter G) := Filter.mem_of_superset hvT hF
    obtain ⟨c,hc,hmem⟩ := (v.finite_biUnion_mem_iff F.finite_toSet).mp hh
    exact ⟨c,hmem⟩
  choose c hc using hchoose
  have hfinite : ∀ N, ∃ z ∈ T, ∀ n ≤ N, z ∈ (fun y => c n*y) '' S n := by
    intro N
    have hall : ∀ᶠ z in (v : Filter G), ∀ n : Fin (N+1), z ∈ (fun y => c n.val*y) '' S n.val :=
      Filter.eventually_all.mpr (fun n => hc n.val)
    obtain ⟨z,hz,hzT⟩ := (hall.and hvT).exists
    exact ⟨z,hzT,fun n hn => hz ⟨n,by omega⟩⟩
  obtain ⟨z,hzT,hz⟩ := hsat c hfinite
  refine ⟨z,hzT,(hbasis z).ge_iff.mpr ?_⟩
  intro n hn
  apply Filter.mem_of_superset (hc (n+1))
  intro y hy
  obtain ⟨a,ha,haz⟩ := hz (n+1)
  obtain ⟨b,hb,hby⟩ := hy
  have hai : a⁻¹ ∈ S (n+1) := by
    have : a⁻¹ ∈ (S (n+1))⁻¹ := by simpa using ha
    simpa only [hinv] using this
  have hab : a⁻¹*b ∈ S n := hsq n (by rw [pow_two]; exact Set.mul_mem_mul hai hb)
  refine ⟨a⁻¹*b,hab,?_⟩
  rw [← haz,← hby]
  group

end DirectedCycles
