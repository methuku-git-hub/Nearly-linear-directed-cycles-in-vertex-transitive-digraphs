module

public import DirectedCycles.FibreSpanning

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Every group element together spans its truncated group ring. -/
theorem spansTruncation_univ {G : Type*} [Group G] (D : ℕ) :
    SpansTruncation D (Set.univ : Set G) := by
  simpa only [SpansTruncation,Set.image_univ] using truncated_elements_generate (G := G) D

/-- Full normal-subgroup fibres over a spanning set of quotient points span
the entire truncated group ring. -/
theorem spanning_of_full_cosets {G I : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (D : ℕ) (r : I → G) (W : AddSubgroup (TruncatedGroupRing G D))
    (hquot : SpansTruncation D (Set.range (fun i => QuotientGroup.mk' K (r i))))
    (hfull : ∀ i, ∀ k : K, truncatedElement G D (k.val*r i) ∈ W) : W = ⊤ := by
  let E : Set G := {x | ∃ i, ∃ k : K, x = k.val*r i}
  have hE : SpansTruncation D E := by
    apply spanning_through_fibres K D E
    · have heq : (QuotientGroup.mk' K) '' E = Set.range (fun i => QuotientGroup.mk' K (r i)) := by
        ext x
        constructor
        · rintro ⟨g,⟨i,k,rfl⟩,rfl⟩
          refine ⟨i,?_⟩
          have hk : QuotientGroup.mk' K k.val = 1 := (QuotientGroup.eq_one_iff _).mpr k.property
          rw [map_mul,hk,one_mul]
        · rintro ⟨i,rfl⟩
          refine ⟨r i,⟨i,1,?_⟩,rfl⟩
          simp
      rw [heq]
      exact hquot
    · intro g hg
      obtain ⟨i,k,rfl⟩ := hg
      have heq : {b : K | b.val*(k.val*r i) ∈ E} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro b
        exact ⟨i,b*k,(mul_assoc _ _ _).symm⟩
      rw [heq]
      exact spansTruncation_univ D
  have hle : AddSubgroup.closure (truncatedElement G D '' E) ≤ W := by
    apply W.closure_le.mpr
    rintro x ⟨g,⟨i,k,rfl⟩,rfl⟩
    exact hfull i k
  rw [hE] at hle
  exact top_le_iff.mp hle

end DirectedCycles
