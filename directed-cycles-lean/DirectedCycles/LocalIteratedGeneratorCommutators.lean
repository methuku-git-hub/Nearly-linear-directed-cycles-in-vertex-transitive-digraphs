module

public import DirectedCycles.LocalCentralQuotientData
public import DirectedCycles.LocalMinimalEscape
public import DirectedCycles.LeftGeneratorCommutators

@[expose] public section

set_option autoImplicit false
open scoped commutatorElement
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Actual left-associated generator commutators, with all four-letter
products defined. The level zero consists of the designated generators. -/
inductive GeneratorCommutators (S : Set G) : ℕ → G → Prop
  | base {x : G} : x ∈ S → GeneratorCommutators S 0 x
  | step {n : ℕ} {x y z : G} : GeneratorCommutators S n x → y ∈ S →
      L.Product [x,y,L.inv x,L.inv y] z → GeneratorCommutators S (n+1) z

/-- A defined commutator of commuting elements is the identity. -/
theorem commutator_product_eq_one (hr : L.Reversible) {x y z : G}
    (hcomm : L.Commute x y) (hp : L.Product [x,y,L.inv x,L.inv y] z) : z = L.one := by
  obtain ⟨a,b,ha,hb,hm⟩ := hp.split L (a := [x,y]) (b := [L.inv x,L.inv y]) rfl (by simp) (by simp)
  obtain ⟨v,hxy,hyx⟩ := hcomm
  have hva : v = a := L.unique hxy ((Product.pair_iff L x y a).1 ha)
  have hib : L.mulRel (L.inv x) (L.inv y) (L.inv a) := by simpa only [hva] using hr hyx
  have hbi : b = L.inv a := L.unique ((Product.pair_iff L _ _ _).1 hb) hib
  rw [hbi] at hm
  exact L.unique hm (L.mul_inv a)

end LocalGroupAlgebra
namespace LocalGroupHom
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

theorem generatorCommutators_map (f : LocalGroupHom L M) {S : Set G} {n : ℕ} {x : G}
    (hx : L.GeneratorCommutators S n x) : M.GeneratorCommutators (f.toFun '' S) n (f.toFun x) := by
  induction hx with
  | base hx => exact .base ⟨_,hx,rfl⟩
  | @step n x y z _ hy hp ih =>
    apply LocalGroupAlgebra.GeneratorCommutators.step ih ⟨y,hy,rfl⟩
    simpa only [List.map_cons,List.map_nil,f.map_inv] using hp.map f
end LocalGroupHom

namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

theorem project_eq_one_iff_mem (x : D.small) : D.project x = D.algebra.one ↔ x.val ∈ P := by
  change D.project x = D.project ⟨L.one,D.one_mem⟩ ↔ _
  rw [D.project_eq_iff,D.relation_iff]
  constructor
  · rintro ⟨p,hp,hm⟩
    rw [L.inv_one] at hm
    exact (L.unique hm (L.mul_one x.val)) ▸ hp
  · intro hx
    exact ⟨x.val,hx,by simpa only [L.inv_one] using L.mul_one x.val⟩

/-- The local central extension raises the left-associated commutator step
by at most one. All source commutators use the actual restricting window;
vanishing in the target is converted to membership in the actual central
progression, without generating a larger kernel subgroup. -/
theorem generatorCommutators_central_step (hr : L.Reversible)
    (S : Set D.small) (hcentral : ∀ p ∈ P, ∀ y ∈ S, L.Commute p y.val)
    (c : ℕ)
    (hquot : ∀ x, D.algebra.GeneratorCommutators (D.project '' S) c x → x = D.algebra.one) :
    ∀ x, (L.restrict D.small D.one_mem D.inv_mem).GeneratorCommutators S (c+1) x →
      x = (L.restrict D.small D.one_mem D.inv_mem).one := by
  intro z hz
  cases hz with
  | @step n x y z hx hy hp =>
    have hpx : D.project x = D.algebra.one := by
      apply hquot
      have hh := D.projectionHom.generatorCommutators_map hx
      have he : D.projectionHom.toFun = D.project := rfl
      simpa only [he] using hh
    have hxP := (D.project_eq_one_iff_mem x).1 hpx
    apply Subtype.ext
    apply L.commutator_product_eq_one hr (hcentral x.val hxP y hy)
    have hh := hp.map (LocalGroupHom.inclusion L D.small D.one_mem D.inv_mem)
    exact hh
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
