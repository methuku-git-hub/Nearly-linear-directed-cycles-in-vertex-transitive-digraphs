module

public import DirectedCycles.LocalWordPowerMaps
public import DirectedCycles.LocalProductSplits

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} (L : LocalGroupAlgebra G) (M : LocalGroupAlgebra H)

/-- Bounded actual words in a local target model neighbourhood construct all
source bracketings. Binary source domains and defined associativity are
used explicitly; injectivity of the model map is unnecessary. -/
theorem allProductsDefined_of_local_model_words (A B : Set G) (hA1 : L.one ∈ A)
    (hBA : B ⊆ A) (hdom : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y)
    (π : LocalGroupHom L M) (W : Set H)
    (hsmall : ∀ x, π.toFun x ∈ W → x ∈ A) (N : ℕ)
    (hwords : ∀ l : List G, l.length ≤ N → (∀ b ∈ l, b ∈ B) →
      ∀ z : H, M.Product (l.map π.toFun) z → z ∈ W) :
    L.AllProductsDefined B N ∧ ∀ n ≤ N, L.wordPower B n ⊆ A := by
  have all : ∀ n : ℕ, n ≤ N → ∀ l : List G, l.length = n →
      (∀ b ∈ l, b ∈ B) → ∃ x ∈ A, L.Product l x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn l hlen hl
      cases l with
      | nil => exact ⟨L.one,hA1,Product.nil⟩
      | cons a l =>
        by_cases hnil : l = []
        · subst l
          exact ⟨a,hBA (hl a (by simp)),Product.singleton a⟩
        have hall : ∀ k : List G, k.length < n → (∀ b ∈ k, b ∈ B) → ∃ x ∈ A, L.Product k x :=
          fun k hk hkb => ih k.length hk (by omega) k rfl hkb
        have hlmem : ∀ b ∈ l, b ∈ B := fun b hb => hl b (List.mem_cons_of_mem a hb)
        have hal : a ∈ A := hBA (hl a (by simp))
        obtain ⟨v,hv,hpv⟩ := hall l (by simp only [List.length_cons] at hlen; omega) hlmem
        obtain ⟨z,hz⟩ := hdom a hal v hv
        have hpz : L.Product (a::l) z := by
          apply Product.of_splits L (by simp only [List.length_cons]; have := List.length_pos_iff.mpr hnil; omega)
          intro p q he hp hq
          cases p with
          | nil => exact (hp rfl).elim
          | cons b p =>
            have he' : a = b ∧ l = p++q := List.cons.inj (by simpa only [List.cons_append] using he)
            obtain ⟨hab,htail⟩ := he'
            subst b
            have hqpos : 0 < q.length := List.length_pos_iff.mpr hq
            have hlength : n = 1+p.length+q.length := by
              simp only [htail,List.length_append,List.length_cons] at hlen
              omega
            have hpmem : ∀ x ∈ p, x ∈ B := fun x hx => hlmem x (htail ▸ List.mem_append_left q hx)
            have hqmem : ∀ x ∈ q, x ∈ B := fun x hx => hlmem x (htail ▸ List.mem_append_right p hx)
            have hapmem : ∀ x ∈ a::p, x ∈ B := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hl x (by simp)
              · exact hpmem x hx
            obtain ⟨u,hu,hpu⟩ := hall p (by omega) hpmem
            obtain ⟨w,hw,hpw⟩ := hall q (by omega) hqmem
            obtain ⟨t,ht,hpt⟩ := hall (a::p) (by simp only [List.length_cons]; omega) hapmem
            obtain ⟨a',u',ha',hu',hau⟩ := hpt.split_allow_empty L (show a::p = [a]++p from rfl)
            have hea : a' = a := (Product.singleton_iff L).1 ha'
            have heu : u' = u := hu'.unique L hpu
            have hat : L.mulRel a u t := by simpa only [hea,heu] using hau
            obtain ⟨u',w',hu',hw',huw⟩ := hpv.split_allow_empty L htail
            have heu' : u' = u := hu'.unique L hpu
            have hew : w' = w := hw'.unique L hpw
            have huv : L.mulRel u w v := by simpa only [heu',hew] using huw
            obtain ⟨z',hz'⟩ := hdom t ht w hw
            have hez : z' = z := L.assoc hat huv hz' hz
            exact ⟨t,w,hpt,hpw,hez ▸ hz'⟩
        refine ⟨z,hsmall z ?_,hpz⟩
        exact hwords (a::l) (hlen ▸ hn) hl (π.toFun z) (hpz.map π)
  refine ⟨?_,?_⟩
  · intro l hlen hl
    obtain ⟨x,_,hp⟩ := all l.length hlen l rfl hl
    exact ⟨x,hp⟩
  · intro n hn x hx
    obtain ⟨l,hlen,hl,hp⟩ := hx
    obtain ⟨y,hy,hpy⟩ := all n hn l hlen hl
    exact (hpy.unique L hp) ▸ hy
end LocalGroupAlgebra
end DirectedCycles
