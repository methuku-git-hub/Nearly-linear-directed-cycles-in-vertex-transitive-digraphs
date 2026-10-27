module

public import DirectedCycles.SeriesCounts
public import DirectedCycles.AbelianRank

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The factor of an intersected normal series embeds in the ambient factor. -/
def intersectedFactorMap {G : Type*} [Group G] (U A B : Subgroup G) [B.Normal] :
    (A.subgroupOf U) ⧸ (B.subgroupOf U).subgroupOf (A.subgroupOf U) →*
      A ⧸ B.subgroupOf A := by
  let f : A.subgroupOf U →* A := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  exact QuotientGroup.lift ((B.subgroupOf U).subgroupOf (A.subgroupOf U))
    ((QuotientGroup.mk' (B.subgroupOf A)).comp f) (by
      intro x hx
      exact (QuotientGroup.eq_one_iff (f x)).mpr hx)

theorem intersectedFactorMap_injective {G : Type*} [Group G]
    (U A B : Subgroup G) [B.Normal] : Function.Injective (intersectedFactorMap U A B) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ((B.subgroupOf U).subgroupOf (A.subgroupOf U)) x
  apply (QuotientGroup.eq_one_iff g).mpr
  exact (QuotientGroup.eq_one_iff (⟨g.val.val, g.property⟩ : A)).mp hx

/-- A finite subgroup of an abelian target has no larger generator rank. -/
theorem rank_le_of_injective_into_abelian {G A : Type*} [Group G] [CommGroup A]
    [Finite G] [Finite A] (f : G →* A) (hf : Function.Injective f) : Group.rank G ≤ Group.rank A := by
  have e := MonoidHom.ofInjective hf
  rw [Group.rank_congr e]
  exact finite_abelian_subgroup_rank_le f.range

/-- Any subgroup inherits the sum of the ranks of the abelian factors in
a normal series. -/
theorem subgroup_rank_le_sum_series_factors {G : Type*} [Group G] [Finite G]
    (H : ℕ → Subgroup G) [∀ i, (H i).Normal] (hd : ∀ i, H (i + 1) ≤ H i)
    (c : ℕ) (h0 : H 0 = ⊤) (hc : H c = ⊥)
    [∀ i, IsMulCommutative (SeriesFactor H i)] (U : Subgroup G) :
    Group.rank U ≤ ∑ i ∈ Finset.range c, Group.rank (SeriesFactor H i) := by
  let J : ℕ → Subgroup U := fun i => (H i).subgroupOf U
  have hJd : ∀ i, J (i + 1) ≤ J i := fun i => Subgroup.subgroupOf_mono U (hd i)
  have hJ0 : J 0 = ⊤ := by simp only [J, h0, Subgroup.top_subgroupOf]
  have hJc : J c = ⊥ := by simp only [J, hc, Subgroup.bot_subgroupOf]
  apply (rank_le_sum_series_factors J hJd c hJ0 hJc).trans
  apply Finset.sum_le_sum
  intro i _
  let : CommGroup (SeriesFactor H i) := { (inferInstance : Group (SeriesFactor H i)) with mul_comm := mul_comm' }
  exact rank_le_of_injective_into_abelian (intersectedFactorMap U (H i) (H (i + 1)))
    (intersectedFactorMap_injective U (H i) (H (i + 1)))

end DirectedCycles
