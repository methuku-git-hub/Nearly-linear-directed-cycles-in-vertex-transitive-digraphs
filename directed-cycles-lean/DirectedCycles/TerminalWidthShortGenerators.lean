module

public import DirectedCycles.TerminalSubgroupMap
public import DirectedCycles.MultihomShortGenerators
public import DirectedCycles.AbelianizationShortGenerators

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace MarkedCommutatorWord

set_option maxHeartbeats 800000 in
/-- A terminal subgroup commutator image has bounded width once short
abelianization generators and a rank bound for its short values are supplied.
Both structural hypotheses are explicit in this theorem. -/
theorem terminal_width_of_short_generators {α : Type*} [Fintype α] [DecidableEq α]
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (w : MarkedCommutatorWord α)
    (hw : w.leafLabels.Nodup) (hall : ∀ i, i ∈ w.leafLabels)
    (hnext : relativeSeries (Subgroup.normalClosure (H : Set G)) (w.degree+1) = ⊥)
    (A : Set G) (U : Subgroup (Abelianization G)) (k : ℕ) (x : Fin k → G)
    (hU : (U : Set (Abelianization G)) ⊆ Abelianization.of '' (A^4))
    (hx : ∀ i, x i ∈ A^4)
    (hgen : Subgroup.closure ((U : Set (Abelianization G)) ∪
      Set.range (fun i => Abelianization.of (x i))) = ⊤)
    (T : Subgroup G) (hTc : T ≤ Subgroup.center G) (r M : ℕ) (hr : Group.rank T ≤ r)
    (hshort : ∀ h : H, ∀ y : α → G, (∀ i, y i ∈ A^4) →
      w.eval h.val y ∈ T ∧ w.eval h.val y ∈ A^M) :
    (Subgroup.closure (Set.range (subgroupTerminalMultihom H w hw hall hnext)) : Set G) ⊆
      A^((k+1)^Fintype.card α*(M*r)) := by
  classical
  let : CommGroup (Subgroup.center G) := { (inferInstance : Group (Subgroup.center G)) with
    mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.property b.val).symm) }
  let : ∀ i : Option α, Finite (Input H α i) := fun i => by cases i <;> infer_instance
  let : ∀ i : Option α, Finite (Abelianization (Input H α i)) := fun i =>
    Finite.of_surjective (Abelianization.of : Input H α i → Abelianization (Input H α i))
      (QuotientGroup.mk'_surjective (commutator (Input H α i)))
  let φ₀ := subgroupTerminalMultihom H w hw hall hnext
  let φ := φ₀.codRestrict (Subgroup.center G) (subgroupTerminalMultihom_central H w hw hall hnext)
  let β := φ.abelianizationDom
  let P : ∀ i : Option α, Subgroup (Abelianization (Input H α i))
    | none => ⊤
    | some _ => U
  let sizes : Option α → ℕ | none => 0 | some _ => k
  let generators : ∀ i : Option α, Fin (sizes i) → Abelianization (Input H α i)
    | none => Fin.elim0
    | some _ => fun j => Abelianization.of (x j)
  have hgenerate : ∀ i, Subgroup.closure ((P i : Set _) ∪ Set.range (generators i)) = ⊤ := by
    intro i
    cases i with
    | none => simp [P]
    | some i => exact hgen
  have hbase : ∀ z, (∀ i, z i ∈ P i ∨ z i ∈ Set.range (generators i)) →
      (β z).val ∈ T ∧ (β z).val ∈ A^M := by
    intro z hz
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (commutator H) (z none)
    have hlift : ∀ i : α, ∃ g ∈ A^4, Abelianization.of g = z (some i) := by
      intro i
      rcases hz (some i) with hi | ⟨j,hj⟩
      · exact hU hi
      · exact ⟨x j,hx j,hj⟩
    choose y hy he using hlift
    let v : ∀ i : Option α, Input H α i | none => a | some i => y i
    have hv : (fun i => Abelianization.of (v i)) = z := by
      funext i
      cases i with
      | none => exact ha
      | some i => exact he i
    have hb : β z = φ v := by
      rw [← hv]
      exact φ.abelianizationDom_apply_of v
    rw [hb]
    exact hshort a y hy
  let Tc := T.subgroupOf (Subgroup.center G)
  have hrc : Group.rank Tc ≤ r := by
    rw [Group.rank_congr (Subgroup.subgroupOfEquivOfLe hTc)]
    exact hr
  let D : Set (Subgroup.center G) := (Subgroup.center G).subtype ⁻¹' (A^M)
  have hb := β.range_width_of_subgroup_and_generators P sizes generators hgenerate ⟨none,rfl⟩
    Tc r 1 hrc D (fun z hz => (hbase z hz).1)
    (fun z hz => by rw [pow_one]; exact (hbase z hz).2)
  have hprod : (∏ i : Option α, (sizes i+1)) = (k+1)^Fintype.card α := by
    simp [Fintype.prod_option,sizes]
  rw [hprod,one_mul] at hb
  have hrange : (Subgroup.center G).subtype '' Set.range β = Set.range φ₀ := by
    rw [show Set.range β = Set.range φ from φ.abelianizationDom_range]
    ext g
    constructor
    · rintro ⟨z,⟨a,rfl⟩,rfl⟩; exact ⟨a,rfl⟩
    · rintro ⟨a,rfl⟩; exact ⟨φ a,⟨a,rfl⟩,rfl⟩
  have hclosure : (Subgroup.closure (Set.range β)).map (Subgroup.center G).subtype =
      Subgroup.closure (Set.range φ₀) := by rw [MonoidHom.map_closure,hrange]
  intro g hg
  have him : g ∈ (Subgroup.closure (Set.range β)).map (Subgroup.center G).subtype := hclosure.symm ▸ hg
  obtain ⟨z,hz,rfl⟩ := him
  have hp : (Subgroup.center G).subtype z ∈
      (Subgroup.center G).subtype '' (D^((k+1)^Fintype.card α*r)) := ⟨z,hb hz,rfl⟩
  rw [Set.image_pow] at hp
  have hD : (Subgroup.center G).subtype '' D ⊆ A^M := Set.image_preimage_subset _ _
  have hpow := Set.pow_subset_pow_left hD hp
  rw [← pow_mul] at hpow
  convert hpow using 1
  congr 1
  ring

end MarkedCommutatorWord
end DirectedCycles
