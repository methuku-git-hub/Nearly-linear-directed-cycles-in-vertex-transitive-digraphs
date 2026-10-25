module

public import DirectedCycles.LocalProductRestriction

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A particular long word restricts to a local window when every subword
value lies in that window. Domain control is proved for the actual word,
without requiring an unrelated full power of the alphabet to stay inside. -/
theorem mapped_product_restrict_of_subwords (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) {α : Type*} (f : α → S) (l : List α) (x : S)
    (hp : L.Product (l.map (fun a => (f a).val)) x.val)
    (hclosed : ∀ q : List α, q.Sublist l → ∀ y : G,
      L.Product (q.map (fun a => (f a).val)) y → y ∈ S) :
    (L.restrict S h1 hi).Product (l.map f) x := by
  have all : ∀ n : ℕ, ∀ q : List α, q.length = n → ∀ y : S,
      L.Product (q.map (fun a => (f a).val)) y.val →
      (∀ a : List α, a.Sublist q → ∀ z : G, L.Product (a.map (fun b => (f b).val)) z → z ∈ S) →
      (L.restrict S h1 hi).Product (q.map f) y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hlen y hq hc
      by_cases hn : q.length ≤ 1
      · cases q with
        | nil =>
          have he : y = (L.restrict S h1 hi).one := Subtype.ext ((Product.nil_iff L).1 hq)
          exact he.symm ▸ Product.nil
        | cons a q =>
          have he : q = [] := by simpa using hn
          subst q
          have hey : y = f a := Subtype.ext ((Product.singleton_iff L).1 hq)
          exact hey.symm ▸ Product.singleton (f a)
      · apply (mapped_product_iff_finite_splits (L.restrict S h1 hi) f (by omega)).2
        intro k hk hk'
        obtain ⟨u,v,hu,hv,hm⟩ := (mapped_product_iff_finite_splits L (fun a => (f a).val) (by omega)).1 hq k hk hk'
        have hua : u ∈ S := hc (q.take k.val) (List.take_sublist k.val q) u hu
        have hva : v ∈ S := hc (q.drop k.val) (List.drop_sublist k.val q) v hv
        refine ⟨⟨u,hua⟩,⟨v,hva⟩,?_,?_,hm⟩
        · apply ih (q.take k.val).length (by simp only [List.length_take]; omega) (q.take k.val) rfl ⟨u,hua⟩ hu
          intro a ha z hz
          exact hc a (ha.trans (List.take_sublist k.val q)) z hz
        · apply ih (q.drop k.val).length (by simp only [List.length_drop]; omega) (q.drop k.val) rfl ⟨v,hva⟩ hv
          intro a ha z hz
          exact hc a (ha.trans (List.drop_sublist k.val q)) z hz
  exact all l.length l rfl x hp hclosed
end LocalGroupAlgebra
end DirectedCycles
