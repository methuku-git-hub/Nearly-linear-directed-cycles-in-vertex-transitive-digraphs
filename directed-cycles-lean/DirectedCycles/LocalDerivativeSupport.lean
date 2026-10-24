import DirectedCycles.LocalConvolutionTranslation
import DirectedCycles.LocalWordPowerMonotonicity

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A translated function is supported only on actual products of its
translating element with its original support. -/
theorem leftShift_support (hc : L.Cancellative) {f : G → ℝ} {B : Set G}
    (hf : ∀ y, y ∉ B → f y = 0) (g : G) {x : G}
    (hx : x ∉ L.setMul {g} B) : L.leftShift g f x = 0 := by
  by_contra h
  obtain ⟨y,hy,hfy⟩ := (L.leftShift_ne_zero_iff hc g f x).1 h
  have hyB : y ∈ B := by by_contra hn; exact hfy (hf y hn)
  exact hx ⟨g,rfl,y,hyB,hy⟩

/-- The derivative of a bump supported in A squared is supported in A cubed,
using only the certified three-letter domain. -/
theorem derivative_support_cube (hc : L.Cancellative) {A : Set G}
    (hA : L.one ∈ A) (hdom : L.AllProductsDefined A 3)
    {f : G → ℝ} (hf : ∀ x, x ∉ L.wordPower A 2 → f x = 0)
    {g : G} (hg : g ∈ A) {x : G} (hx : x ∉ L.wordPower A 3) :
    L.derivative g f x = 0 := by
  have hx2 : x ∉ L.wordPower A 2 :=
    fun h => hx (L.wordPower_subset_wordPower hA hdom (by omega : 2 ≤ 3) le_rfl h)
  have hs : x ∉ L.setMul {g} (L.wordPower A 2) := by
    rintro ⟨a,ha,b,hb,hm⟩
    have he : a = g := ha
    apply hx
    rw [show 3 = 1+2 by rfl,L.wordPower_add hdom (by omega),L.wordPower_one]
    exact ⟨g,hg,b,hb,he ▸ hm⟩
  simp only [derivative,Pi.sub_apply,L.leftShift_support hc hf g hs,hf x hx2,sub_self]
end LocalGroupAlgebra
end DirectedCycles
