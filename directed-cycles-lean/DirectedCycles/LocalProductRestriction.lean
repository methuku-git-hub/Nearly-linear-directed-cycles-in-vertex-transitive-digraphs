import DirectedCycles.LocalWordPowerMaps
import DirectedCycles.LocalProductSplits

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
    (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)

/-- Restricting a local group preserves a bounded word domain when every
subword value is proved to stay in the restricting set. -/
theorem allProductsDefined_restrict {A : Set G} {N : ℕ}
    (hdef : L.AllProductsDefined A N)
    (hS : ∀ n ≤ N, L.wordPower A n ⊆ S) :
    (L.restrict S h1 hi).AllProductsDefined (Subtype.val ⁻¹' A) N := by
  let M := L.restrict S h1 hi
  let f := LocalGroupHom.inclusion L S h1 hi
  have all : ∀ n : ℕ, n ≤ N → ∀ l : List S, l.length = n →
      (∀ a ∈ l, a.val ∈ A) → ∃ x, M.Product l x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn l hlen hl
      by_cases hsmall : l.length ≤ 1
      · cases l with
        | nil => exact ⟨M.one,Product.nil⟩
        | cons a l =>
          have he : l = [] := by simpa using hsmall
          subst l
          exact ⟨a,Product.singleton a⟩
      · have hmap : ∀ a ∈ l.map Subtype.val, a ∈ A := by
          intro a ha
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
          exact hl b hb
        obtain ⟨x,hx⟩ := hdef (l.map Subtype.val)
          (by simpa only [List.length_map,hlen] using hn) hmap
        have hxS : x ∈ S := hS n hn ⟨l.map Subtype.val,by simpa only [List.length_map] using hlen,hmap,hx⟩
        refine ⟨⟨x,hxS⟩,Product.of_splits M (by omega) ?_⟩
        intro a b hab ha hb
        have hlen' : a.length+b.length = n := by simpa only [hab,List.length_append] using hlen
        have hal : 0 < a.length := List.length_pos_iff.mpr ha
        have hbl : 0 < b.length := List.length_pos_iff.mpr hb
        obtain ⟨u,hu⟩ := ih a.length (by omega) (by omega) a rfl (by
          intro z hz
          exact hl z (hab ▸ List.mem_append_left b hz))
        obtain ⟨v,hv⟩ := ih b.length (by omega) (by omega) b rfl (by
          intro z hz
          exact hl z (hab ▸ List.mem_append_right a hz))
        obtain ⟨u',v',hu',hv',hm⟩ := hx.split_allow_empty L
          (a := a.map Subtype.val) (b := b.map Subtype.val)
          (by simp only [hab,List.map_append])
        have heu : u' = u.val := hu'.unique L (hu.map f)
        have hev : v' = v.val := hv'.unique L (hv.map f)
        refine ⟨u,v,hu,hv,?_⟩
        change L.mulRel u.val v.val x
        simpa only [heu,hev] using hm
  exact fun l hlen hl => all l.length hlen l rfl hl

/-- Within this bounded domain, restriction neither loses nor creates word
values; its inclusion has precisely the original word-power image. -/
theorem wordPower_restrict_image {A : Set G} {N n : ℕ}
    (hdef : L.AllProductsDefined A N)
    (hS : ∀ m ≤ N, L.wordPower A m ⊆ S) (hAS : A ⊆ S) (hn : n ≤ N) :
    Subtype.val '' ((L.restrict S h1 hi).wordPower (Subtype.val ⁻¹' A) n) =
      L.wordPower A n := by
  have h := wordPower_image (LocalGroupHom.inclusion L S h1 hi)
    (L.allProductsDefined_restrict S h1 hi hdef hS) hn
  have he : (Subtype.val : S → G) '' (Subtype.val ⁻¹' A) = A := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x,hAS hx⟩,hx,rfl⟩
  simpa only [LocalGroupHom.inclusion,he] using h
end LocalGroupAlgebra
end DirectedCycles
