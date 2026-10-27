module

public import DirectedCycles.LocalGroupProducts
public import DirectedCycles.LocalQuotientOperations

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A map preserves every defined multiplication, but is not required to send
undefined products to undefined products. -/
structure LocalGroupHom {G H : Type*} (L : LocalGroupAlgebra G) (M : LocalGroupAlgebra H) where
  toFun : G → H
  map_one : toFun L.one = M.one
  map_inv : ∀ x, toFun (L.inv x) = M.inv (toFun x)
  map_mul : ∀ {x y z}, L.mulRel x y z → M.mulRel (toFun x) (toFun y) (toFun z)

namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

/-- All-bracketings products are preserved by an actual local homomorphism. -/
theorem Product.map (f : LocalGroupHom L M) {l : List G} {x : G} (h : L.Product l x) :
    M.Product (l.map f.toFun) (f.toFun x) := by
  induction h with
  | nil => simpa only [List.map_nil,f.map_one] using Product.nil (L := M)
  | singleton a => exact Product.singleton (f.toFun a)
  | @splits l x hlen u v left right multiply ihl ihr =>
    refine Product.splits (by simpa using hlen)
      (fun a _ => f.toFun (u (l.take a.length) (l.drop a.length)))
      (fun a _ => f.toFun (v (l.take a.length) (l.drop a.length))) ?_ ?_ ?_
    · intro a b hab ha hb
      have htake : (l.take a.length).map f.toFun = a := by rw [List.map_take,hab,List.take_left]
      have hdrop : (l.drop a.length).map f.toFun = b := by rw [List.map_drop,hab,List.drop_left]
      have hta : l.take a.length ≠ [] := fun he => ha (by simpa [he] using htake.symm)
      have hdb : l.drop a.length ≠ [] := fun he => hb (by simpa [he] using hdrop.symm)
      have hh := ihl _ _ (List.take_append_drop a.length l).symm hta hdb
      simpa only [htake] using hh
    · intro a b hab ha hb
      have htake : (l.take a.length).map f.toFun = a := by rw [List.map_take,hab,List.take_left]
      have hdrop : (l.drop a.length).map f.toFun = b := by rw [List.map_drop,hab,List.drop_left]
      have hta : l.take a.length ≠ [] := fun he => ha (by simpa [he] using htake.symm)
      have hdb : l.drop a.length ≠ [] := fun he => hb (by simpa [he] using hdrop.symm)
      have hh := ihr _ _ (List.take_append_drop a.length l).symm hta hdb
      simpa only [hdrop] using hh
    · intro a b hab ha hb
      have htake : (l.take a.length).map f.toFun = a := by rw [List.map_take,hab,List.take_left]
      have hdrop : (l.drop a.length).map f.toFun = b := by rw [List.map_drop,hab,List.drop_left]
      have hta : l.take a.length ≠ [] := fun he => ha (by simpa [he] using htake.symm)
      have hdb : l.drop a.length ≠ [] := fun he => hb (by simpa [he] using hdrop.symm)
      exact f.map_mul (multiply _ _ (List.take_append_drop a.length l).symm hta hdb)
end LocalGroupAlgebra

namespace LocalGroupHom
variable {G H J : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H} {N : LocalGroupAlgebra J}

def id (L : LocalGroupAlgebra G) : LocalGroupHom L L where
  toFun := _root_.id
  map_one := rfl
  map_inv _ := rfl
  map_mul h := h

def comp (g : LocalGroupHom M N) (f : LocalGroupHom L M) : LocalGroupHom L N where
  toFun := g.toFun ∘ f.toFun
  map_one := by simp only [Function.comp_apply,f.map_one,g.map_one]
  map_inv x := by simp only [Function.comp_apply,f.map_inv,g.map_inv]
  map_mul h := g.map_mul (f.map_mul h)

def inclusion (L : LocalGroupAlgebra G) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : LocalGroupHom (L.restrict S h1 hi) L where
  toFun := Subtype.val
  map_one := rfl
  map_inv _ := rfl
  map_mul h := h
end LocalGroupHom
end DirectedCycles
