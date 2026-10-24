import DirectedCycles.LocalFiniteConvolution
import DirectedCycles.LocalTranslationComposition

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} [Fintype G] (L : LocalGroupAlgebra G)

theorem leftShift_eq_sum (hc : L.Cancellative) (g : G) (f : G → ℝ) (x : G)
    [DecidablePred (fun a => L.mulRel g a x)] :
    L.leftShift g f x = ∑ a : G, if L.mulRel g a x then f a else 0 := by
  classical
  by_cases h : ∃ a, L.mulRel g a x
  · obtain ⟨a,ha⟩ := h
    rw [L.leftShift_of_mulRel hc ha]
    symm
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left ha]
    · intro b _ hba
      exact ite_eq_right (fun hb => hba (hc.left_cancel hb ha))
    · simp
  · rw [L.leftShift_of_no_preimage h]
    symm
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun ha => h ⟨a,ha⟩)

theorem sum_mulRel_output {g a b : G} (hm : L.mulRel g a b) (f : G → ℝ) [DecidablePred (L.mulRel g a)] :
    (∑ x : G, if L.mulRel g a x then f x else 0) = f b := by
  classical
  rw [Finset.sum_eq_single b]
  · rw [ite_eq_left hm]
  · intro x _ hxb
    exact ite_eq_right (fun hx => hxb (L.unique hx hm))
  · simp

/-- Moving a local translation through the first convolution factor is
justified by the three-letter domain on the actual supports. -/
theorem convolution_leftShift (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g : G} (hg : g ∈ R)
    (f k : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R) (hk : ∀ x, k x ≠ 0 → x ∈ R) :
    L.convolution (L.leftShift g f) k = L.leftShift g (L.convolution f k) := by
  classical
  funext x
  have hright : L.leftShift g (L.convolution f k) x =
      ∑ a : G, f a * L.leftShift g (L.leftShift a k) x := by
    change L.leftShift g (fun z => ∑ a : G, f a*L.leftShift a k z) x = _
    rw [L.leftShift_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact congrFun (L.leftShift_const_mul g (f a) (L.leftShift a k)) x
  rw [hright]
  simp only [convolution,L.leftShift_eq_sum hc g f,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = 0
  · simp only [ha,ite_self,zero_mul,Finset.sum_const_zero]
  · have haR := hf a ha
    obtain ⟨b,hb⟩ := hdom [g,a] (by simp) (by aesop)
    have hm : L.mulRel g a b := (Product.pair_iff L _ _ _).1 hb
    have he : (∑ y : G, (if L.mulRel g a y then f a else 0)*L.leftShift y k x) =
        f a * ∑ y : G, if L.mulRel g a y then L.leftShift y k x else 0 := by
      simp only [Finset.mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
    rw [he,L.sum_mulRel_output hm]
    rw [L.leftShift_mul hc hdom hg haR hm k hk]

theorem derivative_convolution (hc : L.Cancellative) {R : Set G}
    (hdom : L.AllProductsDefined R 3) {g : G} (hg : g ∈ R)
    (f k : G → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ R) (hk : ∀ x, k x ≠ 0 → x ∈ R) :
    L.derivative g (L.convolution f k) = L.convolution (L.derivative g f) k := by
  simp only [derivative,L.convolution_sub_left,L.convolution_leftShift hc hdom hg f k hf hk]
end LocalGroupAlgebra
end DirectedCycles
