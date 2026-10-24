import DirectedCycles.LocalOrderedGrid
import DirectedCycles.LocalEscapeNorm

set_option autoImplicit false
namespace DirectedCycles

/-- Embed a smaller signed box into the larger one by retaining its actual
integer coordinates. -/
def SignedCoordinates.weaken {r : ℕ} {M N : Fin r → ℕ} (hMN : ∀ i, M i ≤ N i)
    (k : SignedCoordinates M) : SignedCoordinates N :=
  fun i => ⟨(k i).val,(mem_signedCoordinateInterval _ _).2 ((k.bound i).trans (hMN i))⟩

theorem SignedCoordinates.weaken_injective {r : ℕ} {M N : Fin r → ℕ} (hMN : ∀ i, M i ≤ N i) :
    Function.Injective (SignedCoordinates.weaken hMN) := by
  intro k l he
  funext i
  apply Subtype.ext
  exact congrArg (fun a => (a i).val) he

namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem SignedWordsIn.mono {r : ℕ} {g : Fin r → G} {M N : Fin r → ℕ} {S T : Set G}
    (h : L.SignedWordsIn g N S) (hMN : ∀ i, M i ≤ N i) (hST : S ⊆ T) :
    L.SignedWordsIn g M T := by
  intro w hw
  obtain ⟨x,hx,hp⟩ := h w (fun i => (hw i).trans (hMN i))
  exact ⟨x,hST hx,hp⟩

/-- Properness persists under coordinate shrinking and a change of the
containing window, because both grids use the same unique local products. -/
theorem orderedGrid_injective_of_le {r : ℕ} {g : Fin r → G} {M N : Fin r → ℕ} {S T : Set G}
    (hs : L.SignedWordsIn g M S) (ht : L.SignedWordsIn g N T)
    (hMN : ∀ i, M i ≤ N i) (hinj : Function.Injective (L.orderedGrid ht)) :
    Function.Injective (L.orderedGrid hs) := by
  intro k l he
  apply SignedCoordinates.weaken_injective hMN
  apply hinj
  apply Subtype.ext
  have hk := (L.orderedGrid_product hs k).unique L (L.orderedGrid_product ht (k.weaken hMN))
  have hl := (L.orderedGrid_product hs l).unique L (L.orderedGrid_product ht (l.weaken hMN))
  rw [← hk,← hl]
  exact congrArg Subtype.val he

/-- Changing only the containing set preserves properness, without
changing the coordinate type or reindexing the grid. -/
theorem orderedGrid_injective_change_set {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S T : Set G}
    (hs : L.SignedWordsIn g N S) (ht : L.SignedWordsIn g N T)
    (hinj : Function.Injective (L.orderedGrid ht)) : Function.Injective (L.orderedGrid hs) := by
  intro k l he
  apply hinj
  apply Subtype.ext
  have hk := (L.orderedGrid_product hs k).unique L (L.orderedGrid_product ht k)
  have hl := (L.orderedGrid_product hs l).unique L (L.orderedGrid_product ht l)
  exact hk.symm.trans ((congrArg Subtype.val he).trans hl)

/-- Bounded signed-word domains provide the actual positive generator
powers required by the escape-controlled lifting theorem. -/
theorem SignedWordsIn.generator_powers {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Set G}
    (h : L.SignedWordsIn g N S) (i : Fin r) (n : ℕ) (hn : n ≤ N i) :
    L.PowerIn S (g i) n := by
  obtain ⟨x,hx,hp⟩ := h (List.replicate n (i,true)) (fun j => by
    simp only [List.countP_replicate]
    split_ifs with he
    · have hij : i = j := by simpa using he
      subst j
      exact hn
    · exact Nat.zero_le _)
  refine ⟨x,hx,?_⟩
  simpa only [signedLetters,List.map_replicate,ite_eq_left] using hp
theorem SignedWordsIn.generator_mem {r : ℕ} {g : Fin r → G} {N : Fin r → ℕ} {S : Set G}
    (h : L.SignedWordsIn g N S) (i : Fin r) (hi : 1 ≤ N i) : g i ∈ S :=
  (L.powerIn_one S (g i)).1 (h.generator_powers L i 1 hi)
end LocalGroupAlgebra
end DirectedCycles
