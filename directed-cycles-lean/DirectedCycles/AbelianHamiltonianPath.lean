import DirectedCycles.AbelianPathExtension

set_option autoImplicit false
namespace DirectedCycles

/-- A finite list of available generators gives a forward Hamiltonian path on
its generated subgroup. No inverse labels are introduced. -/
theorem abelian_generated_hamiltonian_path {G : Type*} [CommGroup G] [Finite G]
    (T : Finset G) : ∃ P : List G, P.Nodup ∧ P.head? = some 1 ∧
      P.IsChain (CayleyDigraph (T : Set G)) ∧
      ∀ x, x ∈ P ↔ x ∈ Subgroup.closure (T : Set G) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨[1],by simp,rfl,List.isChain_singleton _,?_⟩
    intro x
    simp
  | @insert a T ha ih =>
    obtain ⟨P,hnd,hh,hc,hm⟩ := ih
    obtain ⟨L,hL,hhead,hchain,hmem⟩ :=
      abelian_path_extension (Subgroup.closure (T : Set G)) (T : Set G) a P hnd hh hc hm
    refine ⟨L,hL,hhead,?_,?_⟩
    · simpa only [Finset.coe_insert] using hchain
    · intro x
      simpa only [Finset.coe_insert,Set.insert_eq,Subgroup.closure_union,
        ← Subgroup.zpowers_eq_closure,sup_comm] using hmem x

/-- Hamiltonian paths in finite abelian directed Cayley graphs, including the
one-vertex path for the trivial group. This proves the literature input used
by the manuscript rather than postulating it. -/
theorem abelian_hamiltonian_path {G : Type*} [CommGroup G] [Finite G]
    (S : Set G) (hgen : Subgroup.closure S = ⊤) :
    ∃ P : List G, P.Nodup ∧ P.head? = some 1 ∧ P.IsChain (CayleyDigraph S) ∧
      ∀ x, x ∈ P := by
  classical
  obtain ⟨P,hnd,hh,hc,hm⟩ := abelian_generated_hamiltonian_path S.toFinite.toFinset
  have he : (S.toFinite.toFinset : Set G) = S := S.toFinite.coe_toFinset
  rw [he,hgen] at hm
  refine ⟨P,hnd,hh,?_,fun x => (hm x).mpr (Subgroup.mem_top x)⟩
  simpa only [he] using hc

/-- The cardinality of an exact enumeration, independent of a chosen Fintype. -/
theorem list_length_eq_natCard {V : Type*} (P : List V)
    (hnd : P.Nodup) (hmem : ∀ x, x ∈ P) : P.length = Nat.card V := by
  have hi : Function.Injective P.get := List.nodup_iff_injective_get.mp hnd
  have hs : Function.Surjective P.get := by
    intro x
    exact List.mem_iff_get.mp (hmem x)
  simpa only [Nat.card_fin] using Nat.card_congr (Equiv.ofBijective P.get ⟨hi,hs⟩)

end DirectedCycles
