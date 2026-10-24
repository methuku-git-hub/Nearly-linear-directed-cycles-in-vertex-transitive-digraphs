import DirectedCycles.LocalUnregularizedEscapeBump
import DirectedCycles.LocalProductSplits
import DirectedCycles.LocalTwoProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- If the total escape cost is small, every bracketing actually exists and
stays in A. This closes the undefined-product case of the local product
estimate; no existence of the final product is assumed. -/
theorem small_word_product_exists {A : Set G} (hA : L.one ∈ A)
    (hdom : ∀ a ∈ A, ∀ b ∈ A, L.Defined a b) {P : ℝ} (hP : 1 ≤ P)
    (hbound : ∀ g, L.escapeNorm A g ≤ P*L.restrictedProductNorm A (L.escapeNorm A) g)
    (l : List G) (hsmall : P*(l.map (L.escapeNorm A)).sum < 1) :
    ∃ x ∈ A, L.Product l x ∧ L.RestrictedProductCost A (L.escapeNorm A) x (l.map (L.escapeNorm A)).sum := by
  have hP0 : 0 ≤ P := by linarith
  have hw := L.escapeNorm_nonneg hA
  have hsum : ∀ q : List G, 0 ≤ (q.map (L.escapeNorm A)).sum := by
    intro q
    exact List.sum_nonneg (by
      intro r hr
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hr
      exact hw g)
  have all : ∀ n : ℕ, ∀ q : List G, q.length = n → P*(q.map (L.escapeNorm A)).sum < 1 →
      ∃ x ∈ A, L.Product q x ∧ L.RestrictedProductCost A (L.escapeNorm A) x (q.map (L.escapeNorm A)).sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hlen hq
      cases q with
      | nil => exact ⟨L.one,hA,Product.nil,by simpa using RestrictedProductCost.one⟩
      | cons g t =>
        have htlen : t.length < n := by simp only [List.length_cons] at hlen; omega
        have htsmall : P*(t.map (L.escapeNorm A)).sum < 1 := by
          have hh : P*(t.map (L.escapeNorm A)).sum ≤ P*(L.escapeNorm A g+(t.map (L.escapeNorm A)).sum) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hw g)) hP0
          exact hh.trans_lt (by simpa only [List.map_cons,List.sum_cons] using hq)
        obtain ⟨v,hvA,hv,hvc⟩ := ih t.length htlen t rfl htsmall
        have hgA : g ∈ A := by
          apply L.mem_of_escapeNorm_lt_one hA
          have hgcost : L.escapeNorm A g ≤ (g::t |>.map (L.escapeNorm A)).sum := by
            simp only [List.map_cons,List.sum_cons]
            exact le_add_of_nonneg_right (hsum t)
          have hgP : L.escapeNorm A g ≤ P*L.escapeNorm A g :=
            le_mul_of_one_le_left (hw g) hP
          exact hgP.trans_lt ((mul_le_mul_of_nonneg_left hgcost hP0).trans_lt hq)
        obtain ⟨x,hm⟩ := hdom g hgA v hvA
        have hcost : L.RestrictedProductCost A (L.escapeNorm A) x ((g::t).map (L.escapeNorm A)).sum := by
          simpa only [List.map_cons,List.sum_cons] using
            RestrictedProductCost.mul (RestrictedProductCost.leaf g) hvc hgA hvA hm
        have hxA : x ∈ A := L.mem_of_escapeNorm_lt_one hA
          (((hbound x).trans (mul_le_mul_of_nonneg_left (L.restrictedProductNorm_le_cost hw hcost) hP0)).trans_lt hq)
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
          have htotal : ((g::t).map (L.escapeNorm A)).sum =
              (a.map (L.escapeNorm A)).sum+(b.map (L.escapeNorm A)).sum := by
            rw [hab,List.map_append,List.sum_append]
          have hasmall : P*(a.map (L.escapeNorm A)).sum < 1 :=
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hsum b)) hP0).trans_lt (htotal ▸ hq)
          have hbsmall : P*(b.map (L.escapeNorm A)).sum < 1 :=
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hsum a)) hP0).trans_lt (htotal ▸ hq)
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
