import DirectedCycles.MultihomSubgroupWidth

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

set_option maxHeartbeats 600000 in
/-- The central part of the normal-envelope argument. A bounded-rank central
subgroup containing a short separately homomorphic image yields an actual
normal subgroup with a uniform power bound. -/
theorem central_multihom_envelope {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B : ι → Type*} [∀ i, Group (B i)] [∀ i, Finite (B i)]
    {G : Type*} [Group G] [Finite G]
    (φ : GroupMultihom B (Subgroup.center G)) (H : Subgroup (Subgroup.center G))
    (hH : Set.range φ ⊆ H) (r M : ℕ) (hr : Group.rank H ≤ r)
    (A : Set G) (hA : (Subgroup.center G).subtype '' Set.range φ ⊆ A^M) :
    ∃ N : Subgroup G, N.Normal ∧ N ≤ Subgroup.center G ∧
      (Subgroup.center G).subtype '' Set.range φ ⊆ N ∧ (N : Set G) ⊆ A^(M*r) := by
  let : CommGroup (Subgroup.center G) := { (inferInstance : Group (Subgroup.center G)) with
    mul_comm := fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp x.property y.val).symm) }
  let K := Subgroup.closure (Set.range φ)
  let N := K.map (Subgroup.center G).subtype
  have hc : N ≤ Subgroup.center G := by
    rintro g ⟨x,_,rfl⟩
    exact x.property
  refine ⟨N,Subgroup.normal_of_le_center hc,hc,?_,?_⟩
  · rintro g ⟨x,hx,rfl⟩
    exact ⟨x,Subgroup.subset_closure hx,rfl⟩
  · rintro g ⟨x,hx,rfl⟩
    have hwidth := GroupMultihom.finite_range_width_in_subgroup
      (G := Subgroup.center G) φ H hH r hr
    have hp := hwidth hx
    have him : (Subgroup.center G).subtype x ∈
        (Subgroup.center G).subtype '' ((Set.range φ)^r) := ⟨x,hp,rfl⟩
    rw [Set.image_pow] at him
    have hh := Set.pow_subset_pow_left (n := r) hA him
    simpa only [← pow_mul] using hh

end DirectedCycles
