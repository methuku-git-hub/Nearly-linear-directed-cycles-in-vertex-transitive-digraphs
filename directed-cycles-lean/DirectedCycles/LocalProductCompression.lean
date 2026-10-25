module

public import DirectedCycles.LocalProductSplits
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Compressing consecutive fully defined blocks preserves every bracketing.
Empty blocks are permitted and compress to the identity. -/
theorem Product.compress {blocks : List (List G)} {values : List G} {x : G}
    (hblocks : List.Forall₂ L.Product blocks values)
    (hflat : L.Product blocks.flatten x) : L.Product values x := by
  have all : ∀ n : ℕ, ∀ values : List G, values.length = n →
      ∀ blocks : List (List G), List.Forall₂ L.Product blocks values →
        ∀ x, L.Product blocks.flatten x → L.Product values x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro values hlen blocks hb x hx
      by_cases hsmall : values.length ≤ 1
      · cases hb with
        | nil => exact hx
        | @cons block value blocks values hp hrest =>
          have hv : values = [] := by simpa using hsmall
          subst values
          cases hrest
          have hx' : L.Product block x := by simpa using hx
          have he : x = value := hx'.unique L hp
          exact he.symm ▸ Product.singleton value
      · apply Product.of_splits L (by omega)
        intro a b he ha hb'
        have hal : 0 < a.length := List.length_pos_iff.mpr ha
        have hbl : 0 < b.length := List.length_pos_iff.mpr hb'
        have hn : n = a.length+b.length := by simpa only [he,List.length_append] using hlen.symm
        have hba : List.Forall₂ L.Product (blocks.take a.length) a :=
          List.forall₂_take_append blocks a b (he ▸ hb)
        have hbb : List.Forall₂ L.Product (blocks.drop a.length) b :=
          List.forall₂_drop_append blocks a b (he ▸ hb)
        have hsplit : blocks.flatten =
            (blocks.take a.length).flatten ++ (blocks.drop a.length).flatten := by
          rw [← List.flatten_append,List.take_append_drop]
        obtain ⟨u,v,hu,hv,hm⟩ := hx.split_allow_empty L hsplit
        exact ⟨u,v,ih a.length (by omega) a rfl _ hba u hu,
          ih b.length (by omega) b rfl _ hbb v hv,hm⟩
  exact all values.length values rfl blocks hblocks x hflat

/-- Fully defined words in A also justify words of words, with the exact
multiplicative length budget. -/
theorem AllProductsDefined.wordPower {A : Set G} {N m n : ℕ}
    (hdom : L.AllProductsDefined A N) (hmn : m*n ≤ N) :
    L.AllProductsDefined (L.wordPower A m) n := by
  intro values hlen hmem
  have blocks : ∃ bs : List (List G), List.Forall₂ L.Product bs values ∧
      (∀ b ∈ bs, b.length = m ∧ ∀ a ∈ b, a ∈ A) := by
    induction values with
    | nil => exact ⟨[],List.Forall₂.nil,by simp⟩
    | cons x xs ih =>
      obtain ⟨b,hbl,hb,hp⟩ := hmem x (by simp)
      obtain ⟨bs,hbs,ha⟩ := ih (by simp only [List.length_cons] at hlen; omega)
        (fun a h => hmem a (List.mem_cons_of_mem x h))
      refine ⟨b::bs,List.Forall₂.cons hp hbs,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hbl,hb⟩
      · exact ha c hc
  obtain ⟨bs,hbs,hb⟩ := blocks
  have hlength : bs.flatten.length = m*values.length := by
    have hgeneral : ∀ bs : List (List G), (∀ b ∈ bs, b.length = m) →
        bs.flatten.length = m*bs.length := by
      intro bs hs
      induction bs with
      | nil => simp
      | cons b bs ih =>
        rw [List.flatten_cons,List.length_append,hs b (by simp),
          ih (fun c hc => hs c (List.mem_cons_of_mem b hc)),List.length_cons]
        ring
    rw [hgeneral bs (fun b hb' => (hb b hb').1),hbs.length_eq]
  have hflatmem : ∀ a ∈ bs.flatten, a ∈ A := by
    intro a ha
    obtain ⟨b,hb',ha⟩ := List.mem_flatten.mp ha
    exact (hb b hb').2 a ha
  obtain ⟨x,hx⟩ := hdom bs.flatten (by rw [hlength]; exact (Nat.mul_le_mul_left m hlen).trans hmn) hflatmem
  exact ⟨x,hx.compress L hbs⟩
end LocalGroupAlgebra
end DirectedCycles
