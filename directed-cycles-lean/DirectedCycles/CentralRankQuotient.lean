import DirectedCycles.AbelianShortGeneration

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- The first central quotient in terminal peeling. The bound r is uniform
in the ambient finite group. The abelian inverse assertion remains an
explicit premise until it has been proved. -/
theorem central_rank_quotient_of_abelian_input (hAb : FiniteAbelianShortGeneration)
    (K : ℝ) (hK : 1 ≤ K) (p : ℕ) (hp : 2 ≤ p) :
    ∃ r : ℕ, ∀ (G : Type) [Group G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A →
      ∃ (Z : Subgroup G) (hZn : Z.Normal),
        letI := hZn
        Z ≤ Subgroup.center G ∧ (Z : Set G) ⊆ A^(p*4) ∧
        ∃ T : Subgroup (G ⧸ Z), T ≤ Subgroup.center (G ⧸ Z) ∧ Group.rank T ≤ r ∧
          (QuotientGroup.mk' Z) '' (A^p ∩ (Subgroup.center G : Set G)) ⊆ T := by
  obtain ⟨r,hstructure⟩ := hAb (K^(2*p-1)) (one_le_pow₀ hK)
  refine ⟨r,?_⟩
  intro G _ _ A hA
  let S := A^p ∩ (Subgroup.center G : Set G)
  let R := Subgroup.closure S
  have hRc : R ≤ Subgroup.center G := (Subgroup.center G).closure_le.mpr Set.inter_subset_right
  let : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hRc x.property) y.val).symm) }
  let B : Set R := R.subtype ⁻¹' (A^p)
  have himage : R.subtype '' B = S := by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨hx,hRc x.property⟩
    · rintro ⟨hg,hc⟩
      exact ⟨⟨g,Subgroup.subset_closure ⟨hg,hc⟩⟩,hg,rfl⟩
  have hBgen : Subgroup.closure B = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [MonoidHom.map_closure,himage,Subgroup.map_top,R.range_subtype]
  have hBapprox : IsApproximateSubgroup (K^(2*p-1)) B :=
    approximate_power_subgroup_preimage A K hA R p hp
  obtain ⟨H,F,hHB,_hFB,hF,hgen⟩ := hstructure R B hBapprox hBgen
  let Z := H.map R.subtype
  have hZc : Z ≤ Subgroup.center G := by
    rintro g ⟨x,_,rfl⟩; exact hRc x.property
  let : Z.Normal := Subgroup.normal_of_le_center hZc
  let q := QuotientGroup.mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  let T := R.map q
  let f := q.subgroupMap R
  have hf : Function.Surjective f := q.subgroupMap_surjective R
  have hker : H ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change q x.val = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x,hx,rfl⟩
  have hrT : Group.rank T ≤ r := (rank_le_generators_mod_kernel f hf H hker F hgen).trans hF
  have hTc : T ≤ Subgroup.center (G ⧸ Z) := by
    rintro g ⟨x,hx,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := hq y
    simpa only [map_mul] using congrArg q (Subgroup.mem_center_iff.mp (hRc hx) z)
  refine ⟨Z,inferInstance,hZc,?_,T,hTc,hrT,?_⟩
  · rintro g ⟨x,hx,rfl⟩
    have him : R.subtype x ∈ R.subtype '' (B^4) := ⟨x,hHB hx,rfl⟩
    rw [Set.image_pow,himage] at him
    have hh := Set.pow_subset_pow_left (n := 4) (Set.inter_subset_left : S ⊆ A^p) him
    simpa only [← pow_mul] using hh
  · rintro g ⟨x,hx,rfl⟩
    exact Subgroup.mem_map_of_mem q (Subgroup.subset_closure hx)

end DirectedCycles
