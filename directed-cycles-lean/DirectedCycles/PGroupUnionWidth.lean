import DirectedCycles.PGroupGeneratingSubset
import DirectedCycles.AbelianRank
import DirectedCycles.FiniteNormalProducts

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A nonempty union of subgroups in a finite abelian p-group has product
width at most the ambient generator rank. The explicit identity hypothesis
includes the degenerate empty-family boundary case. -/
theorem pgroup_union_subgroups_width {G : Type*} [CommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p G)
    (X : Set G) (h1 : 1 ∈ X)
    (hcyc : ∀ x ∈ X, (Subgroup.zpowers x : Set G) ⊆ X) :
    (Subgroup.closure X : Set G) ⊆ X^(Group.rank G) := by
  classical
  let H := Subgroup.closure X
  obtain ⟨T,hT,hcard,hgen⟩ := pgroup_generating_subset_rank p (hP.to_subgroup H)
    (H.subtype ⁻¹' X) (Subgroup.closure_preimage_eq_top X)
  let F : T → Subgroup G := fun t => Subgroup.zpowers t.val.val
  have hF : (⨆ t, F t : Subgroup G) = H := by
    have hm : (Subgroup.closure (T : Set H)).map H.subtype = H := by
      rw [hgen,Subgroup.map_top,H.range_subtype]
    rw [MonoidHom.map_closure] at hm
    apply le_antisymm
    · apply iSup_le
      intro t
      exact Subgroup.zpowers_le.mpr t.val.property
    · calc
        H = Subgroup.closure (H.subtype '' (T : Set H)) := hm.symm
        _ ≤ ⨆ t, F t := by
          apply (⨆ t, F t : Subgroup G).closure_le.mpr
          rintro x ⟨t,ht,rfl⟩
          exact (le_iSup F ⟨t,ht⟩) (Subgroup.mem_zpowers t.val)
  have hb := finite_normal_sup_power_bound X (⊤ : Subgroup G) F 1
    (fun _ => le_top) (fun t => by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (F t).Normal)])
    (fun t => by simpa only [pow_one] using hcyc t.val.val (hT t.property))
  rw [hF] at hb
  intro x hx
  have hh : x ∈ X^T.card := by simpa only [Fintype.card_coe,mul_one] using hb hx
  exact Set.pow_subset_pow_right h1
    (hcard.trans (finite_abelian_subgroup_rank_le H)) hh

end DirectedCycles
