module

public import DirectedCycles.StrongLocalApproximateGroups
public import DirectedCycles.LocalProductSplits
public import DirectedCycles.LocalTwoProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A bound for all actual words constructs every bracketing of a word
whose total escape cost is small. No existence of a long product or
unregularized norm comparison is assumed. -/
theorem small_word_product_exists_of_bound {A : Set G} (hA : L.one ∈ A)
    (hdom : ∀ a ∈ A, ∀ b ∈ A, L.Defined a b) {P : ℝ} (hP : 1 ≤ P)
    (hbound : ∀ (q : List G) (x : G), L.Product q x →
      L.escapeNorm A x ≤ P*(q.map (L.escapeNorm A)).sum)
    (l : List G) (hsmall : P*(l.map (L.escapeNorm A)).sum < 1) :
    ∃ x ∈ A, L.Product l x ∧ L.escapeNorm A x ≤ P*(l.map (L.escapeNorm A)).sum := by
  have hP0 : 0 ≤ P := by linarith
  have hw := L.escapeNorm_nonneg hA
  have hsum : ∀ q : List G, 0 ≤ (q.map (L.escapeNorm A)).sum := by
    intro q
    exact List.sum_nonneg (by
      intro r hr
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hr
      exact hw g)
  have all : ∀ n : ℕ, ∀ q : List G, q.length = n → P*(q.map (L.escapeNorm A)).sum < 1 →
      ∃ x ∈ A, L.Product q x ∧ L.escapeNorm A x ≤ P*(q.map (L.escapeNorm A)).sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hlen hq
      cases q with
      | nil => exact ⟨L.one,hA,Product.nil,by simp only [L.escapeNorm_one hA,List.map_nil,List.sum_nil,mul_zero,le_refl]⟩
      | cons g t =>
        have htlen : t.length < n := by simp only [List.length_cons] at hlen; omega
        have htsmall : P*(t.map (L.escapeNorm A)).sum < 1 := by
          have hh : P*(t.map (L.escapeNorm A)).sum ≤ P*(L.escapeNorm A g+(t.map (L.escapeNorm A)).sum) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hw g)) hP0
          exact hh.trans_lt (by simpa only [List.map_cons,List.sum_cons] using hq)
        obtain ⟨v,hvA,hv,_hvc⟩ := ih t.length htlen t rfl htsmall
        have hgA : g ∈ A := by
          apply L.mem_of_escapeNorm_lt_one hA
          have hgcost : L.escapeNorm A g ≤ (g::t |>.map (L.escapeNorm A)).sum := by
            simp only [List.map_cons,List.sum_cons]
            exact le_add_of_nonneg_right (hsum t)
          have hgP : L.escapeNorm A g ≤ P*L.escapeNorm A g :=
            le_mul_of_one_le_left (hw g) hP
          exact hgP.trans_lt ((mul_le_mul_of_nonneg_left hgcost hP0).trans_lt hq)
        obtain ⟨x,hm⟩ := hdom g hgA v hvA
        suffices hp : L.Product (g::t) x from
          ⟨x,L.mem_of_escapeNorm_lt_one hA ((hbound _ _ hp).trans_lt hq),hp,hbound _ _ hp⟩
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

/-- Finite strong local approximate groups have actual products for every
word of small total escape, using the proved uniform Gleason bound. -/
theorem strong_local_small_word_exists {G : Type*} [Fintype G]
    (L : LocalGroupAlgebra G) (hd : L.DivisionClosed) (hr : L.Reversible)
    {K : ℕ} {A : Finset G} (hA : IsStrongLocalFiniteApproximateGroup L K A)
    (l : List G)
    (hsmall : (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (L.escapeNorm A)).sum < 1) :
    ∃ x ∈ A, L.Product l x ∧ L.escapeNorm A x ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map (L.escapeNorm A)).sum := by
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hA.approximate.one_le
  have hKnat : 1 ≤ K^3 := by
    have hh : 0 < K := by have := hA.approximate.one_le; omega
    have := pow_pos hh 3
    omega
  have hconstant : (1 : ℝ) ≤ 8*1000*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ) := by
    have hc : (1 : ℝ) ≤ ((1000000*K^3 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 1000000*K^3 by omega)
    nlinarith [mul_le_mul hK hc (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ K)]
  apply L.small_word_product_exists_of_bound hA.approximate.one_mem _ hconstant
    (fun _ _ hp => strong_local_approximate_product L hd hr hA hp) l hsmall
  intro a ha b hb
  obtain ⟨z,hz⟩ := hA.approximate.allProducts [a,b] (by simp) (by aesop)
  exact ⟨z,(LocalGroupAlgebra.Product.pair_iff L a b z).1 hz⟩
end DirectedCycles
