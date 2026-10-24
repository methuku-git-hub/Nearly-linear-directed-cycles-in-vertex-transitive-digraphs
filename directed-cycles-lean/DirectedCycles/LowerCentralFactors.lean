import DirectedCycles.CentralCommutators
import DirectedCycles.Subquotients
import DirectedCycles.SeriesCounts
import Mathlib.GroupTheory.Nilpotent

set_option autoImplicit false
open scoped Classical commutatorElement
namespace DirectedCycles

abbrev lowerSeries (G : Type*) [Group G] : ℕ → Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries

abbrev LowerCentralFactor (G : Type*) [Group G] (i : ℕ) :=
  (lowerSeries G i) ⧸ (lowerSeries G (i + 1)).subgroupOf (lowerSeries G i)

theorem lowerSeries_map {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (i : ℕ) :
    (lowerSeries G i).map f = lowerSeries Q i := by
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective f hf]

/-- Surjections preserve lower central factors surjectively. -/
theorem exists_surjective_lowerFactorMap {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (i : ℕ) :
    ∃ F : LowerCentralFactor G i →* LowerCentralFactor Q i, Function.Surjective F := by
  have : ((lowerSeries G (i + 1)).map f).Normal := Subgroup.Normal.map inferInstance f hf
  let e := QuotientGroup.equivQuotientSubgroupOfOfEq (lowerSeries_map f hf (i + 1)) (lowerSeries_map f hf i)
  exact ⟨e.toMonoidHom.comp (subgroupQuotientMap f (lowerSeries G i) (lowerSeries G (i + 1))),
    e.surjective.comp (subgroupQuotientMap_surjective f _ _)⟩

/-- Killing the next lower central subgroup makes the current one central. -/
theorem lowerSeries_central_mod_next (G : Type*) [Group G] (i : ℕ) :
    lowerSeries (G ⧸ lowerSeries G (i + 1)) i ≤ Subgroup.center (G ⧸ lowerSeries G (i + 1)) := by
  let f := QuotientGroup.mk' (lowerSeries G (i + 1))
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  change lowerSeries (G ⧸ lowerSeries G (i + 1)) (i + 1) = ⊥
  rw [← lowerSeries_map f hf]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']

/-- The rank of a successive central factor is at most the preceding factor
rank times the number of generators of the original group. -/
theorem lowerFactor_rank_step (G : Type*) [Group G] [Finite G] (i : ℕ) :
    Group.rank (LowerCentralFactor G (i + 1)) ≤
      Group.rank (LowerCentralFactor G i) * Group.rank G := by
  let Q := G ⧸ lowerSeries G (i + 1 + 1)
  let f := QuotientGroup.mk' (lowerSeries G (i + 1 + 1))
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  let A := lowerSeries Q i
  let B := lowerSeries Q (i + 1)
  have hB : B ≤ Subgroup.center Q := lowerSeries_central_mod_next G (i + 1)
  have hcent : ⁅A, (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := hB
  have hZ : ∀ z : B.subgroupOf A, z.val.val ∈ Subgroup.center Q := fun z => hB z.property
  have h := central_commutator_rank_le A hcent (B.subgroupOf A) hZ
  change Group.rank B ≤ Group.rank (LowerCentralFactor Q i) * Group.rank Q at h
  obtain ⟨F, hF⟩ := exists_surjective_lowerFactorMap f hf i
  have hrF := Group.rank_le_of_surjective F hF
  have hrQ := Group.rank_le_of_surjective f hf
  have he : Group.rank (LowerCentralFactor G (i + 1)) = Group.rank B := by
    calc Group.rank (LowerCentralFactor G (i + 1)) =
          Group.rank ((lowerSeries G (i + 1)).map f) :=
            Group.rank_congr (subgroupQuotientEquivMap (lowerSeries G (i + 1)) (lowerSeries G (i + 1 + 1)))
         _ = Group.rank B := Subgroup.rank_congr (lowerSeries_map f hf (i + 1))
  rw [he]
  exact h.trans (Nat.mul_le_mul hrF hrQ)

/-- Every lower central factor has the manuscript's stated generator bound. -/
theorem lowerFactor_rank_bound (G : Type*) [Group G] [Finite G] (i : ℕ) :
    Group.rank (LowerCentralFactor G i) ≤ Group.rank G ^ (i + 1) := by
  induction i with
  | zero =>
    have h := Group.rank_le_of_surjective (QuotientGroup.mk' ((lowerSeries G 1).subgroupOf (lowerSeries G 0)))
      (QuotientGroup.mk'_surjective _)
    change Group.rank (LowerCentralFactor G 0) ≤ Group.rank (⊤ : Subgroup G) at h
    rw [Group.rank_congr Subgroup.topEquiv] at h
    simpa using h
  | succ i ih =>
    exact (lowerFactor_rank_step G i).trans (by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _ ih)

/-- Lower central factors are abelian, directly from the defining commutator
inclusion. -/
instance lowerFactor_isMulCommutative (G : Type*) [Group G] (i : ℕ) :
    IsMulCommutative (LowerCentralFactor G i) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  have hm : (commutator (lowerSeries G i)).map (lowerSeries G i).subtype =
      ⁅lowerSeries G i, lowerSeries G i⁆ := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.subtype_range]
  intro x hx
  have him : x.val ∈ (commutator (lowerSeries G i)).map (lowerSeries G i).subtype := ⟨x,hx,rfl⟩
  rw [hm] at him
  exact Subgroup.commutator_mono le_rfl le_top him

/-- Every lower central factor inherits the exponent of the abelianization. -/
theorem lowerFactor_exponent (G : Type*) [Group G] (e : ℕ)
    (he : ∀ a : Abelianization G, a ^ e = 1) (i : ℕ) :
    ∀ x : LowerCentralFactor G i, x ^ e = 1 := by
  cases i with
  | zero =>
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ((lowerSeries G 1).subgroupOf (lowerSeries G 0)) x
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change g.val ^ e ∈ commutator G
    apply (QuotientGroup.eq_one_iff _).mp
    exact (map_pow Abelianization.of g.val e).trans (he (Abelianization.of g.val))
  | succ i =>
    let Q := G ⧸ lowerSeries G (i + 1 + 1)
    let f := QuotientGroup.mk' (lowerSeries G (i + 1 + 1))
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
    let A := lowerSeries Q i
    let B := lowerSeries Q (i + 1)
    have hB : B ≤ Subgroup.center Q := lowerSeries_central_mod_next G (i + 1)
    have hcent : ⁅A, (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := hB
    have hp := central_commutator_subgroup_exponent A hcent e
      (abelianization_exponent_of_surjective f hf e he)
    let E : LowerCentralFactor G (i + 1) ≃* B :=
      (subgroupQuotientEquivMap (lowerSeries G (i + 1)) (lowerSeries G (i + 1 + 1))).trans
        (MulEquiv.subgroupCongr (lowerSeries_map f hf (i + 1)))
    intro x
    apply E.injective
    rw [map_pow, map_one]
    exact hp (E x)

end DirectedCycles
