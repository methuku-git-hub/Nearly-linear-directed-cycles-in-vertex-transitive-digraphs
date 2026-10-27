module

public import DirectedCycles.LocalGroupAlgebra

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A local finite product requires valid products for every contiguous split,
recursively, and the same value at each split. This does not identify arbitrary
bracketings merely because a left-associated computation happens to exist. -/
inductive Product : List G → G → Prop
  | nil : Product [] L.one
  | singleton (a : G) : Product [a] a
  | splits {l : List G} {x : G} (hlen : 2 ≤ l.length)
      (u v : List G → List G → G)
      (left : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → Product a (u a b))
      (right : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → Product b (v a b))
      (multiply : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → L.mulRel (u a b) (v a b) x) : Product l x

theorem Product.nil_iff {x : G} : L.Product [] x ↔ x = L.one := by
  constructor
  · intro h
    cases h with
    | nil => rfl
    | splits hlen _ _ _ _ _ => simp at hlen
  · rintro rfl
    exact Product.nil

theorem Product.singleton_iff {a x : G} : L.Product [a] x ↔ x = a := by
  constructor
  · intro h
    cases h with
    | singleton => rfl
    | splits hlen _ _ _ _ _ => simp at hlen
  · rintro rfl
    exact Product.singleton _

theorem Product.split {l a b : List G} {x : G} (h : L.Product l x)
    (hl : l = a++b) (ha : a ≠ []) (hb : b ≠ []) :
    ∃ u v : G, L.Product a u ∧ L.Product b v ∧ L.mulRel u v x := by
  have hal : 0 < a.length := List.length_pos_iff.mpr ha
  have hbl : 0 < b.length := List.length_pos_iff.mpr hb
  cases h with
  | nil => have hh := congrArg List.length hl; simp only [List.length_nil,List.length_append] at hh; omega
  | singleton => have hh := congrArg List.length hl; simp only [List.length_cons,List.length_nil,List.length_append] at hh; omega
  | splits _ u v hleft hright hmul => exact ⟨u a b,v a b,hleft a b hl ha hb,hright a b hl ha hb,hmul a b hl ha hb⟩

theorem Product.unique {l : List G} {x y : G} (hx : L.Product l x) (hy : L.Product l y) : x = y := by
  have all : ∀ n : ℕ, ∀ l : List G, l.length = n → ∀ x y,
      L.Product l x → L.Product l y → x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen x y hx hy
      cases l with
      | nil => exact (Product.nil_iff L).1 hx |>.trans ((Product.nil_iff L).1 hy).symm
      | cons a l =>
        cases l with
        | nil => exact ((Product.singleton_iff L).1 hx).trans ((Product.singleton_iff L).1 hy).symm
        | cons b l =>
          obtain ⟨u,v,hu,hv,huv⟩ := hx.split L (a := [a]) (b := b::l) rfl (by simp) (by simp)
          obtain ⟨u',v',hu',hv',huv'⟩ := hy.split L (a := [a]) (b := b::l) rfl (by simp) (by simp)
          have huu : u = u' := ((Product.singleton_iff L).1 hu).trans ((Product.singleton_iff L).1 hu').symm
          have hvv : v = v' := ih (b::l).length (by simp only [List.length_cons] at hlen ⊢; omega)
            (b::l) rfl v v' hv hv'
          rw [huu,hvv] at huv
          exact L.unique huv huv'
  exact all l.length l rfl x y hx hy

/-- All finite products in a global group satisfy the local product definition. -/
theorem ofGroup_product (G : Type*) [Group G] (l : List G) : (ofGroup G).Product l l.prod := by
  have all : ∀ n : ℕ, ∀ l : List G, l.length = n → (ofGroup G).Product l l.prod := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen
      by_cases hn : l.length ≤ 1
      · cases l with
        | nil => exact Product.nil
        | cons a l =>
          have hl : l = [] := by simpa using hn
          subst l
          simpa using Product.singleton (L := ofGroup G) a
      · refine Product.splits (by omega) (fun a _ => a.prod) (fun _ b => b.prod) ?_ ?_ ?_
        · intro a b hab ha hb
          have hbl : 0 < b.length := List.length_pos_iff.mpr hb
          have hlen' : a.length+b.length = n := by simpa [hab] using hlen
          exact ih a.length (by omega) a rfl
        · intro a b hab ha hb
          have hal : 0 < a.length := List.length_pos_iff.mpr ha
          have hlen' : a.length+b.length = n := by simpa [hab] using hlen
          exact ih b.length (by omega) b rfl
        · intro a b hab _ _
          change a.prod*b.prod = l.prod
          simp [hab]
  exact all l.length l rfl

theorem ofGroup_product_iff (G : Type*) [Group G] (l : List G) (x : G) :
    (ofGroup G).Product l x ↔ x = l.prod := by
  constructor
  · intro hx
    exact hx.unique (ofGroup G) (ofGroup_product G l)
  · rintro rfl
    exact ofGroup_product G l
end LocalGroupAlgebra
end DirectedCycles
