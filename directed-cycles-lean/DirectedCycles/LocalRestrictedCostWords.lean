import DirectedCycles.LocalRestrictedProductNorm
import DirectedCycles.LocalWordPowers
import DirectedCycles.LocalOptimalEscapeBump

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Every fully defined word either admits an A-restricted cost tree, or
contains a cost tree whose value leaves A and whose cost is no larger than
that of the whole word. This records the first failure of the restricted
domain instead of multiplying estimates outside their range of validity. -/
theorem Product.restrictedCost_or_exit {A : Set G} {w : G → ℝ}
    (hw : ∀ g, 0 ≤ w g) {l : List G} {x : G} (hp : L.Product l x) :
    L.RestrictedProductCost A w x (l.map w).sum ∨
      ∃ y r, y ∉ A ∧ L.RestrictedProductCost A w y r ∧ r ≤ (l.map w).sum := by
  induction l generalizing x with
  | nil =>
    have he := (Product.nil_iff L).1 hp
    subst x
    exact Or.inl (by simpa using RestrictedProductCost.one)
  | cons g l ih =>
    obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (a := [g]) (b := l) rfl
    have he := (Product.singleton_iff L).1 hu
    subst u
    have hl0 : 0 ≤ (l.map w).sum := List.sum_nonneg (by
      intro r hr
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hr
      exact hw a)
    rcases ih hv with hc | ⟨y,r,hy,hc,hcost⟩
    · by_cases hg : g ∈ A
      · by_cases hvA : v ∈ A
        · exact Or.inl (by simpa only [List.map_cons,List.sum_cons] using
            RestrictedProductCost.mul (RestrictedProductCost.leaf g) hc hg hvA hm)
        · exact Or.inr ⟨v,(l.map w).sum,hvA,hc,by
            simp only [List.map_cons,List.sum_cons]
            linarith [hw g]⟩
      · exact Or.inr ⟨g,w g,hg,RestrictedProductCost.leaf g,by
          simp only [List.map_cons,List.sum_cons]
          linarith⟩
    · exact Or.inr ⟨y,r,hy,hc,by
        simp only [List.map_cons,List.sum_cons]
        linarith [hw g]⟩

/-- Restricted regularized control suffices for every fully defined word.
If a partial cost tree leaves A, its escape is one and controls the escape of
the final word, which is always at most one. -/
theorem escape_word_bound_of_restricted_regularized {A : Set G} (hA : L.one ∈ A)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ∀ g, L.escapeNorm A g ≤ C*L.restrictedEscapeDistance A ε g)
    {l : List G} {x : G} (hp : L.Product l x) :
    L.escapeNorm A x ≤ C*(l.map (L.escapeNorm A)).sum := by
  apply le_of_forall_pos_le_add
  intro η hη
  let t := C*(l.length : ℝ)+1
  have ht : 0 < t := by dsimp [t]; positivity
  let ε := η/t
  have hε : 0 < ε := div_pos hη ht
  let w := fun g => L.escapeNorm A g+ε
  have hw : ∀ g, 0 ≤ w g := fun g => add_nonneg (L.escapeNorm_nonneg hA g) hε.le
  have hbound : L.escapeNorm A x ≤ C*(l.map w).sum := by
    rcases hp.restrictedCost_or_exit L hw with hc | ⟨y,r,hy,hc,hcost⟩
    · exact (h ε hε x).trans (mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_cost hw hc) hC)
    · have hh := (h ε hε y).trans (mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_cost hw hc) hC)
      rw [L.escapeNorm_eq_one_of_not_mem hA hy] at hh
      exact (L.escapeNorm_le_one hA x).trans (hh.trans (mul_le_mul_of_nonneg_left hcost hC))
  have he : ∀ q : List G, (q.map w).sum = (q.map (L.escapeNorm A)).sum+(q.length : ℝ)*ε := by
    intro q
    induction q with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,ih]
      dsimp [w]
      ring
  rw [he l] at hbound
  have hte : t*ε = η := by dsimp [ε]; field_simp
  have herror : C*(l.length : ℝ)*ε ≤ η := by
    have htC : C*(l.length : ℝ) ≤ t := by dsimp [t]; linarith
    exact (mul_le_mul_of_nonneg_right htC hε.le).trans_eq hte
  nlinarith
end LocalGroupAlgebra
end DirectedCycles
