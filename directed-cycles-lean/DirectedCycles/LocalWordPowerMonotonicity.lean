module

public import DirectedCycles.LocalZeroEscapeSubgroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem wordPower_subset_wordPower {A : Set G} (hA : L.one ∈ A) {N m n : ℕ}
    (hdom : L.AllProductsDefined A N) (hmn : m ≤ n) (hn : n ≤ N) :
    L.wordPower A m ⊆ L.wordPower A n := by
  rintro x ⟨l,hl,ha,hp⟩
  let v := l ++ List.replicate (n-m) L.one
  have hvlen : v.length = n := by simp only [v,List.length_append,List.length_replicate,hl]; omega
  have hvA : ∀ a ∈ v, a ∈ A := by
    intro a h
    rcases List.mem_append.mp h with h | h
    · exact ha a h
    · have he : a = L.one := (List.mem_replicate.mp h).2
      exact he.symm ▸ hA
  obtain ⟨y,hy⟩ := hdom v (hvlen ▸ hn) hvA
  obtain ⟨u,w,hu,hw,hm⟩ := hy.split_allow_empty L rfl
  have heu : u = x := hu.unique L hp
  have hew : w = L.one := hw.unique L (L.product_replicate_one (n-m))
  have hmul : L.mulRel x L.one y := by simpa only [heu,hew] using hm
  have hey : y = x := L.unique hmul (L.mul_one x)
  exact ⟨v,hvlen,hvA,hey ▸ hy⟩

theorem wordPower_subset_of_maximum {A S : Set G} (hA : L.one ∈ A) {N : ℕ}
    (hdom : L.AllProductsDefined A N) (hS : L.wordPower A N ⊆ S) :
    ∀ n ≤ N, L.wordPower A n ⊆ S :=
  fun _ hn => (L.wordPower_subset_wordPower hA hdom hn le_rfl).trans hS
end LocalGroupAlgebra
end DirectedCycles
