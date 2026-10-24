import DirectedCycles.LocalConjugates
import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalTranslationComposition

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The local commutator relation is derived by compressing an actually
fully defined six-letter word and cancelling inverse pairs. -/
theorem commutator_multiplication {A : Set G} (hdom : L.AllProductsDefined A 6)
    {g h r s k : G} (hg : g ∈ A) (hh : h ∈ A)
    (hgi : L.inv g ∈ A) (hhi : L.inv h ∈ A)
    (hr : L.mulRel h g r) (hs : L.mulRel g h s)
    (hk : L.Product [L.inv g,L.inv h,g,h] k) : L.mulRel r k s := by
  obtain ⟨z,hz⟩ := hdom [h,g,L.inv g,L.inv h,g,h] (by simp) (by aesop)
  have hblocks : List.Forall₂ L.Product [[h,g],[L.inv g,L.inv h,g,h]] [r,k] :=
    List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hr) (List.Forall₂.cons hk List.Forall₂.nil)
  have hp : L.Product [r,k] z :=
    (show L.Product ([[h,g],[L.inv g,L.inv h,g,h]] : List (List G)).flatten z from hz).compress L hblocks
  have hc : List.Forall₂ L.Product [[h],[g,L.inv g],[L.inv h],[g,h]] [h,L.one,L.inv h,s] :=
    List.Forall₂.cons (Product.singleton _)
      (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 (L.mul_inv g))
        (List.Forall₂.cons (Product.singleton _)
          (List.Forall₂.cons ((Product.pair_iff L _ _ _).2 hs) List.Forall₂.nil)))
  have ht : L.Product [h,L.one,L.inv h,s] z :=
    (show L.Product ([[h],[g,L.inv g],[L.inv h],[g,h]] : List (List G)).flatten z from hz).compress L hc
  have hc' : List.Forall₂ L.Product [[h,L.one,L.inv h],[s]] [L.one,s] :=
    List.Forall₂.cons (Product.triple_of_rel L (L.mul_one _) (L.one_mul _) (L.mul_inv h) (L.mul_inv h))
      (List.Forall₂.cons (Product.singleton _) List.Forall₂.nil)
  have ht' : L.Product [L.one,s] z :=
    (show L.Product ([[h,L.one,L.inv h],[s]] : List (List G)).flatten z from ht).compress L hc'
  have he : z = s := L.unique ((Product.pair_iff L _ _ _).1 ht') (L.one_mul s)
  exact he ▸ ((Product.pair_iff L _ _ _).1 hp)

/-- The commutator derivative identity uses only three proved translation
compositions. It does not assert a global action of the local group. -/
theorem derivative_commutator_identity (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g h r s k : G}
    (hg : g ∈ R) (hh : h ∈ R) (hr : r ∈ R) (hk : k ∈ R)
    (hhg : L.mulRel h g r) (hgh : L.mulRel g h s) (hrk : L.mulRel r k s)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R) :
    L.leftShift r (L.derivative k f) =
      L.derivative g (L.derivative h f)-L.derivative h (L.derivative g f) := by
  unfold derivative
  simp only [L.leftShift_sub]
  rw [← L.leftShift_mul hc hdom hr hk hrk f hf,
    ← L.leftShift_mul hc hdom hg hh hgh f hf,
    ← L.leftShift_mul hc hdom hh hg hhg f hf]
  ext x
  simp only [Pi.sub_apply]
  ring

variable [Fintype G]

/-- Translation of the commutator derivative is an isometry because its
whole support is proved to lie in the actual translating domain. -/
theorem derivativeNorm_commutator_le (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g h r s k : G}
    (hg : g ∈ R) (hh : h ∈ R) (hr : r ∈ R) (hk : k ∈ R)
    (hhg : L.mulRel h g r) (hgh : L.mulRel g h s) (hrk : L.mulRel r k s)
    (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R) :
    L.derivativeNorm f k ≤ L.derivativeNorm (L.derivative h f) g+L.derivativeNorm (L.derivative g f) h := by
  have hs : ∀ x, L.derivative k f x ≠ 0 → L.Defined r x := by
    intro x hx
    by_cases hfx : f x = 0
    · have hshift : L.leftShift k f x ≠ 0 := by
        simpa only [derivative,Pi.sub_apply,hfx,sub_zero] using hx
      obtain ⟨y,hky,hfy⟩ := (L.leftShift_ne_zero_iff hc k f x).1 hshift
      obtain ⟨z,_,hrx⟩ := hdom.triple L hr hk (hf y hfy) hrk hky
      exact ⟨z,hrx⟩
    · obtain ⟨z,hz⟩ := hdom [r,x] (by simp) (by aesop)
      exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  unfold derivativeNorm
  rw [← L.norm_leftShift_eq hc r (L.derivative k f) hs,
    L.derivative_commutator_identity hc hdom hg hh hr hk hhg hgh hrk f hf]
  exact norm_sub_le _ _
end LocalGroupAlgebra
end DirectedCycles
