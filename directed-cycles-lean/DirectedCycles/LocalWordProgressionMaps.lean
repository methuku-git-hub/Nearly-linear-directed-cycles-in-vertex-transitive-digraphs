module

public import DirectedCycles.LocalSignedWords
public import DirectedCycles.LocalSubwordRestriction
public import DirectedCycles.LocalCentralQuotientData

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupHom
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    (f : LocalGroupHom L M)

theorem map_signedLetters {r : ℕ} (g : Fin r → G) (w : List (Fin r × Bool)) :
    (L.signedLetters g w).map f.toFun = M.signedLetters (fun i => f.toFun (g i)) w := by
  simp only [LocalGroupAlgebra.signedLetters,List.map_map]
  apply List.map_congr_left
  intro a _
  change f.toFun (if a.2 then g a.1 else L.inv (g a.1)) = _
  split
  · rfl
  · exact f.map_inv _

theorem wordProgression_image_subset {r : ℕ} (g : Fin r → G) (N : Fin r → ℕ) :
    f.toFun '' L.wordProgression g N ⊆ M.wordProgression (fun i => f.toFun (g i)) N := by
  rintro _ ⟨x,⟨w,hw,hp⟩,rfl⟩
  refine ⟨w,hw,?_⟩
  simpa only [f.map_signedLetters] using hp.map f
end LocalGroupHom

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
    (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)

theorem signedWord_restrict {r : ℕ} (g : Fin r → S) (N : Fin r → ℕ)
    (hall : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ S, L.Product (L.signedLetters (fun i => (g i).val) w) x)
    (w : List (Fin r × Bool)) (hw : ∀ i, w.countP (fun a => a.1 = i) ≤ N i) (x : S)
    (hp : L.Product (L.signedLetters (fun i => (g i).val) w) x.val) :
    (L.restrict S h1 hi).Product ((L.restrict S h1 hi).signedLetters g w) x := by
  let f : Fin r × Bool → S := fun a => if a.2 then g a.1 else ⟨L.inv (g a.1).val,hi _ (g a.1).property⟩
  have hletters : ∀ q : List (Fin r × Bool), q.map (fun a => (f a).val) =
      L.signedLetters (fun i => (g i).val) q := by
    intro q
    apply List.map_congr_left
    intro a _
    dsimp only [f]
    split <;> rfl
  have hres : (L.restrict S h1 hi).Product (w.map f) x := by
    apply L.mapped_product_restrict_of_subwords S h1 hi f w x (by rw [hletters]; exact hp)
    intro q hq y hy
    obtain ⟨z,hz,hpz⟩ := hall q (fun i => hq.countP_le.trans (hw i))
    rw [hletters] at hy
    exact (hy.unique L hpz).symm ▸ hz
  exact hres

theorem wordProgression_restrict_image {r : ℕ} (g : Fin r → S) (N : Fin r → ℕ)
    (hall : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ S, L.Product (L.signedLetters (fun i => (g i).val) w) x) :
    Subtype.val '' (L.restrict S h1 hi).wordProgression g N =
      L.wordProgression (fun i => (g i).val) N := by
  apply Set.Subset.antisymm
  · exact (LocalGroupHom.inclusion L S h1 hi).wordProgression_image_subset g N
  · rintro x ⟨w,hw,hp⟩
    obtain ⟨y,hy,hpy⟩ := hall w hw
    have hxy : x = y := hp.unique L hpy
    have hxS : x ∈ S := hxy.symm ▸ hy
    exact ⟨⟨x,hxS⟩,⟨w,hw,L.signedWord_restrict S h1 hi g N hall w hw ⟨x,hxS⟩ hp⟩,rfl⟩

namespace CentralQuotientData
variable {L S h1 hi} {P : Set G} (D : L.CentralQuotientData P)

theorem project_signedWord {r : ℕ} (g : Fin r → D.small) (N : Fin r → ℕ)
    (hall : ∀ w : List (Fin r × Bool), (∀ i, w.countP (fun a => a.1 = i) ≤ N i) →
      ∃ x ∈ D.small, L.Product (L.signedLetters (fun i => (g i).val) w) x)
    (w : List (Fin r × Bool)) (hw : ∀ i, w.countP (fun a => a.1 = i) ≤ N i) (x : D.small)
    (hp : L.Product (L.signedLetters (fun i => (g i).val) w) x.val) :
    D.algebra.Product (D.algebra.signedLetters (fun i => D.project (g i)) w) (D.project x) := by
  have hh := (L.signedWord_restrict D.small D.one_mem D.inv_mem g N hall w hw x hp).map D.projectionHom
  rw [D.projectionHom.map_signedLetters] at hh
  have he : D.projectionHom.toFun = D.project := rfl
  rw [he] at hh
  exact hh
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
