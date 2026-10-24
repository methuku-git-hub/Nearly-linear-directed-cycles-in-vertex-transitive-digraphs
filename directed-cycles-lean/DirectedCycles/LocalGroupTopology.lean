import DirectedCycles.LocalGroupAlgebra
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [TopologicalSpace G]

/-- The topological axioms of a local group are imposed on its actual domain
of multiplication. Undefined products never enter the continuity statement. -/
structure LocalGroupTopology (L : LocalGroupAlgebra G) : Prop where
  continuous_inv : Continuous L.inv
  isOpen_domain : IsOpen {p : G × G | L.Defined p.1 p.2}
  continuous_mul : Continuous (fun p : {p : G × G | L.Defined p.1 p.2} =>
    L.mul p.val.1 p.val.2 p.property)

namespace LocalGroupTopology
variable (L : LocalGroupAlgebra G)

theorem ofGroup [Group G] [IsTopologicalGroup G] : LocalGroupTopology (LocalGroupAlgebra.ofGroup G) where
  continuous_inv := ContinuousInv.continuous_inv
  isOpen_domain := by
    have he : {p : G × G | (LocalGroupAlgebra.ofGroup G).Defined p.1 p.2} = Set.univ := by
      ext p; simp [LocalGroupAlgebra.ofGroup_defined]
    rw [he]; exact isOpen_univ
  continuous_mul := by
    have he : (fun p : {p : G × G | (LocalGroupAlgebra.ofGroup G).Defined p.1 p.2} =>
        (LocalGroupAlgebra.ofGroup G).mul p.val.1 p.val.2 p.property) =
        (fun p => p.val.1*p.val.2) := by
      funext p
      exact LocalGroupAlgebra.ofGroup_mul G _ _ _
    rw [he]
    exact continuous_subtype_val.fst.mul continuous_subtype_val.snd

/-- Open symmetric restrictions retain the local topological group axioms. -/
theorem restrict (hL : LocalGroupTopology L) (S : Set G) (hS : IsOpen S)
    (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S) :
    LocalGroupTopology (L.restrict S h1 hi) where
  continuous_inv := (hL.continuous_inv.comp continuous_subtype_val).subtype_mk _
  isOpen_domain := by
    let f : S × S → G × G := fun p => (p.1.val,p.2.val)
    have hf : Continuous f := (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
    let D : Set (S × S) := {p | L.Defined p.1.val p.2.val}
    have hD : IsOpen D := hL.isOpen_domain.preimage hf
    let m : D → G := fun p => L.mul p.val.1.val p.val.2.val p.property
    have hm : Continuous m := hL.continuous_mul.comp
      ((hf.comp continuous_subtype_val).subtype_mk fun p => p.property)
    have he : {p : S × S | (L.restrict S h1 hi).Defined p.1 p.2} =
        Subtype.val '' (m ⁻¹' S) := by
      ext p
      constructor
      · rintro ⟨x,hx⟩
        have hd : L.Defined p.1.val p.2.val := ⟨x.val,hx⟩
        refine ⟨⟨p,hd⟩,?_,rfl⟩
        change L.mul _ _ hd ∈ S
        rw [L.unique (L.mul_spec _ _ hd) hx]
        exact x.property
      · rintro ⟨p,hp,rfl⟩
        exact ⟨⟨m p,hp⟩,L.mul_spec _ _ p.property⟩
    rw [he]
    exact hD.isOpenMap_subtype_val _ (hS.preimage hm)
  continuous_mul := by
    let f : {p : S × S | (L.restrict S h1 hi).Defined p.1 p.2} →
        {p : G × G | L.Defined p.1 p.2} := fun p =>
      ⟨(p.val.1.val,p.val.2.val),by
        obtain ⟨x,hx⟩ := p.property
        exact ⟨x.val,hx⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_subtype_val.fst).prodMk
        (continuous_subtype_val.comp continuous_subtype_val.snd)
    apply continuous_induced_rng.2
    have he : (fun p : {p : S × S | (L.restrict S h1 hi).Defined p.1 p.2} =>
        ((L.restrict S h1 hi).mul p.val.1 p.val.2 p.property).val) =
        (fun p => L.mul (f p).val.1 (f p).val.2 (f p).property) := by
      funext p
      exact L.unique ((L.restrict S h1 hi).mul_spec _ _ p.property) (L.mul_spec _ _ (f p).property)
    change Continuous (fun p : {p : S × S | (L.restrict S h1 hi).Defined p.1 p.2} =>
      ((L.restrict S h1 hi).mul p.val.1 p.val.2 p.property).val)
    rw [he]
    exact hL.continuous_mul.comp hf
end LocalGroupTopology
end DirectedCycles
