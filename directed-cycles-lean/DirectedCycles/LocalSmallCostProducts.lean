module

public import DirectedCycles.LocalProductSplits
public import DirectedCycles.LocalTwoProducts
public import DirectedCycles.LocalWordPowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A local triangle inequality and a small-cost membership criterion force
all bracketings of every sufficiently small-cost word to exist. No global
multiplication or domain for the long word is assumed. -/
theorem small_cost_product_exists {A : Set G} (hA : L.one ∈ A)
    (hdom : ∀ a ∈ A, ∀ b ∈ A, L.Defined a b) (f : G → ℝ)
    (hf : ∀ g, 0 ≤ f g) (h1 : f L.one = 0)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, ∀ c, L.mulRel a b c → f c ≤ f a+f b)
    {r : ℝ} (hmem : ∀ g, f g < r → g ∈ A)
    (l : List G) (hsmall : (l.map f).sum < r) :
    ∃ x ∈ A, L.Product l x ∧ f x ≤ (l.map f).sum := by
  have hsum : ∀ q : List G, 0 ≤ (q.map f).sum := by
    intro q
    exact List.sum_nonneg (by
      intro v hv
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hv
      exact hf g)
  have all : ∀ n : ℕ, ∀ q : List G, q.length = n → (q.map f).sum < r →
      ∃ x ∈ A, L.Product q x ∧ f x ≤ (q.map f).sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hlen hq
      cases q with
      | nil => exact ⟨L.one,hA,Product.nil,by simp only [h1,List.map_nil,List.sum_nil,le_refl]⟩
      | cons g t =>
        have htlen : t.length < n := by simp only [List.length_cons] at hlen; omega
        have htsmall : (t.map f).sum < r :=
          (le_add_of_nonneg_left (hf g)).trans_lt (by simpa only [List.map_cons,List.sum_cons] using hq)
        obtain ⟨v,hvA,hv,hvc⟩ := ih t.length htlen t rfl htsmall
        have hgA : g ∈ A := hmem g
          ((le_add_of_nonneg_right (hsum t)).trans_lt (by simpa only [List.map_cons,List.sum_cons] using hq))
        obtain ⟨x,hm⟩ := hdom g hgA v hvA
        have hcost : f x ≤ ((g::t).map f).sum := by
          simpa only [List.map_cons,List.sum_cons] using
            (hmul g hgA v hvA x hm).trans (add_le_add (le_refl (f g)) hvc)
        have hxA : x ∈ A := hmem x (hcost.trans_lt hq)
        refine ⟨x,hxA,?_,hcost⟩
        by_cases ht : t = []
        · subst t
          have hev := (Product.nil_iff L).1 hv
          rw [hev] at hm
          have hex : x = g := L.unique hm (L.mul_one g)
          exact hex.symm ▸ Product.singleton g
        · apply Product.of_splits L (by simp only [List.length_cons]; have := List.length_pos_iff.mpr ht; omega)
          intro a b hab ha hb
          have hbl : 0 < b.length := List.length_pos_iff.mpr hb
          have hlen' : n = a.length+b.length := by rw [← hlen,hab,List.length_append]
          have htotal : ((g::t).map f).sum = (a.map f).sum+(b.map f).sum := by
            rw [hab,List.map_append,List.sum_append]
          have hasmall : (a.map f).sum < r := (le_add_of_nonneg_right (hsum b)).trans_lt (htotal ▸ hq)
          have hbsmall : (b.map f).sum < r := (le_add_of_nonneg_left (hsum a)).trans_lt (htotal ▸ hq)
          have hal : 0 < a.length := List.length_pos_iff.mpr ha
          obtain ⟨u,huA,hu,_⟩ := ih a.length (by omega) a rfl hasmall
          obtain ⟨w,hwA,hbw,_⟩ := ih b.length (by omega) b rfl hbsmall
          cases a with
          | nil => exact (ha rfl).elim
          | cons a a' =>
            have hcons : g = a ∧ t = a'++b := List.cons.inj hab
            rcases hcons with ⟨rfl,htb⟩
            obtain ⟨u',v',hu',hv',hm'⟩ := hv.split_allow_empty L htb
            have hv'w : v' = w := hv'.unique L hbw
            subst v'
            obtain ⟨a'',u'',ha'',hu'',ham⟩ := hu.split_allow_empty L (a := [g]) (b := a') rfl
            have hea := (Product.singleton_iff L).1 ha''
            subst a''
            have heu : u'' = u' := hu''.unique L hu'
            subst u''
            obtain ⟨z,hz⟩ := hdom u huA w hwA
            have hez : z = x := L.assoc ham hm' hz hm
            exact ⟨u,w,hu,hbw,hez ▸ hz⟩
  exact all l.length l rfl hsmall
end LocalGroupAlgebra
end DirectedCycles
