module

public import DirectedCycles.LocalFiniteTranslations
public import DirectedCycles.LocalTripleProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem leftShift_ne_zero_iff (hL : L.Cancellative) (g : G) (f : G → ℝ) (x : G) :
    L.leftShift g f x ≠ 0 ↔ ∃ y, L.mulRel g y x ∧ f y ≠ 0 := by
  classical
  constructor
  · intro h
    by_cases he : ∃ y, L.mulRel g y x
    · obtain ⟨y,hy⟩ := he
      exact ⟨y,hy,by simpa only [L.leftShift_of_mulRel hL hy] using h⟩
    · exact (h (L.leftShift_of_no_preimage he f)).elim
  · rintro ⟨y,hy,hf⟩
    simpa only [L.leftShift_of_mulRel hL hy] using hf

/-- Composition of local translations agrees with multiplication on a
function whose support lies inside a fully defined three-letter domain. -/
theorem leftShift_mul (hL : L.Cancellative) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {g h gh : G} (hg : g ∈ A) (hh : h ∈ A)
    (hm : L.mulRel g h gh) (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ A) :
    L.leftShift gh f = L.leftShift g (L.leftShift h f) := by
  funext x
  have from_left : L.leftShift gh f x ≠ 0 →
      L.leftShift gh f x = L.leftShift g (L.leftShift h f) x := by
    intro hx
    obtain ⟨a,ha,hfa⟩ := (L.leftShift_ne_zero_iff hL gh f x).1 hx
    obtain ⟨b,hb⟩ := hdom [h,a] (by simp) (by aesop)
    have hha : L.mulRel h a b := (Product.pair_iff L _ _ _).1 hb
    obtain ⟨z,hz,hgz⟩ := hdom.triple L hg hh (hf a hfa) hm hha
    have he : z = x := L.unique hz ha
    rw [he] at hgz
    rw [L.leftShift_of_mulRel hL ha,L.leftShift_of_mulRel hL hgz,L.leftShift_of_mulRel hL hha]
  by_cases hx : L.leftShift gh f x ≠ 0
  · exact from_left hx
  · have hx0 : L.leftShift gh f x = 0 := not_ne_iff.mp hx
    by_cases hy : L.leftShift g (L.leftShift h f) x ≠ 0
    · obtain ⟨b,hgb,hb⟩ := (L.leftShift_ne_zero_iff hL g (L.leftShift h f) x).1 hy
      obtain ⟨a,hha,hfa⟩ := (L.leftShift_ne_zero_iff hL h f b).1 hb
      obtain ⟨z,hz,hgz⟩ := hdom.triple L hg hh (hf a hfa) hm hha
      have he : z = x := L.unique hgz hgb
      rw [he] at hz
      exact (hx ((L.leftShift_ne_zero_iff hL gh f x).2 ⟨a,hz,hfa⟩)).elim
    · exact hx0.trans (not_ne_iff.mp hy).symm

theorem derivative_mul (hL : L.Cancellative) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {g h gh : G} (hg : g ∈ A) (hh : h ∈ A)
    (hm : L.mulRel g h gh) (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ A) :
    L.derivative gh f = L.leftShift g (L.derivative h f) + L.derivative g f := by
  unfold derivative
  rw [L.leftShift_mul hL hdom hg hh hm f hf,L.leftShift_sub]
  ext x
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

section Finite
variable [Fintype G]

theorem derivativeNorm_mul_le (hL : L.Cancellative) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {g h gh : G} (hg : g ∈ A) (hh : h ∈ A)
    (hm : L.mulRel g h gh) (f : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ A) :
    L.derivativeNorm f gh ≤ L.derivativeNorm f g + L.derivativeNorm f h := by
  unfold derivativeNorm
  rw [L.derivative_mul hL hdom hg hh hm f hf]
  exact (norm_add_le _ _).trans ((add_le_add (L.norm_leftShift_le g (L.derivative h f)) le_rfl).trans_eq (add_comm _ _))

theorem derivativeNorm_inv (hd : L.DivisionClosed) (hr : L.Reversible)
    (g : G) (f : G → ℝ)
    (hs : ∀ x, f x ≠ 0 → L.Defined g x)
    (hsi : ∀ x, f x ≠ 0 → L.Defined (L.inv g) x) :
    L.derivativeNorm f (L.inv g) = L.derivativeNorm f g := by
  have step : ∀ g, (∀ x, f x ≠ 0 → L.Defined g x) →
      L.derivativeNorm f (L.inv g) ≤ L.derivativeNorm f g := by
    intro g hg
    have he : L.derivative (L.inv g) f = -L.leftShift (L.inv g) (L.derivative g f) := by
      unfold derivative
      rw [L.leftShift_sub,L.leftShift_inv_leftShift hd hr g f hg]
      ext x
      simp only [Pi.neg_apply,Pi.sub_apply]
      ring
    unfold derivativeNorm
    rw [he,norm_neg]
    exact L.norm_leftShift_le _ _
  exact le_antisymm (step g hs) (by simpa only [L.inv_inv] using step (L.inv g) hsi)
end Finite
end LocalGroupAlgebra
end DirectedCycles
