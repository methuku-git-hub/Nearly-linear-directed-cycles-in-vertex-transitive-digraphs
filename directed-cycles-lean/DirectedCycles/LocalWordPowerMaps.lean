import DirectedCycles.LocalWordPowers
import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles

theorem exists_list_preimage_in {G H : Type*} (f : G → H) (A : Set G) (l : List H)
    (hl : ∀ x ∈ l, x ∈ f '' A) : ∃ v : List G, v.map f = l ∧ ∀ a ∈ v, a ∈ A := by
  induction l with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons x l ih =>
    obtain ⟨a,ha,hax⟩ := hl x (by simp)
    obtain ⟨v,hv,hva⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    refine ⟨a::v,by simp only [List.map_cons,hax,hv],?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hva b hb

namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

theorem wordPower_image_subset (f : LocalGroupHom L M) (A : Set G) (n : ℕ) :
    f.toFun '' (L.wordPower A n) ⊆ M.wordPower (f.toFun '' A) n := by
  rintro y ⟨x,⟨l,hlen,hl,hp⟩,rfl⟩
  refine ⟨l.map f.toFun,by simpa only [List.length_map] using hlen,?_,hp.map f⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact ⟨a,hl a ha,rfl⟩

theorem AllProductsDefined.image {A : Set G} {N : ℕ} (h : L.AllProductsDefined A N)
    (f : LocalGroupHom L M) : M.AllProductsDefined (f.toFun '' A) N := by
  intro l hlen hl
  obtain ⟨v,hv,hva⟩ := exists_list_preimage_in f.toFun A l hl
  obtain ⟨x,hx⟩ := h v (by simpa only [← hv,List.length_map] using hlen) hva
  exact ⟨f.toFun x,by simpa only [hv] using hx.map f⟩

/-- For lengths inside the established source domain, all words in the image
lift, so their value set is the exact image of the original word power. -/
theorem wordPower_image (f : LocalGroupHom L M) {A : Set G} {N n : ℕ}
    (h : L.AllProductsDefined A N) (hn : n ≤ N) :
    f.toFun '' (L.wordPower A n) = M.wordPower (f.toFun '' A) n := by
  apply Set.Subset.antisymm (wordPower_image_subset f A n)
  rintro x ⟨l,hlen,hl,hp⟩
  obtain ⟨v,hv,hva⟩ := exists_list_preimage_in f.toFun A l hl
  have hvlen : v.length = n := by simpa only [← hv,List.length_map] using hlen
  obtain ⟨y,hy⟩ := h v (hvlen ▸ hn) hva
  refine ⟨y,⟨v,hvlen,hva,hy⟩,?_⟩
  have hmap : M.Product l (f.toFun y) := by simpa only [hv] using hy.map f
  exact hmap.unique M hp

theorem setMul_image_subset (f : LocalGroupHom L M) (A B : Set G) :
    f.toFun '' (L.setMul A B) ⊆ M.setMul (f.toFun '' A) (f.toFun '' B) := by
  rintro z ⟨x,⟨a,ha,b,hb,hm⟩,rfl⟩
  exact ⟨f.toFun a,⟨a,ha,rfl⟩,f.toFun b,⟨b,hb,rfl⟩,f.map_mul hm⟩

/-- For sets containing the identity, requiring all words of exactly N
letters is equivalent to requiring all words of length at most N. -/
theorem allProductsDefined_of_exact_length {A : Set G} (hA : L.one ∈ A) {N : ℕ}
    (h : ∀ l : List G, l.length = N → (∀ a ∈ l, a ∈ A) → ∃ x, L.Product l x) :
    L.AllProductsDefined A N := by
  intro l hlen hl
  let v := l ++ List.replicate (N-l.length) L.one
  have hvlen : v.length = N := by simp only [v,List.length_append,List.length_replicate]; omega
  have hva : ∀ a ∈ v, a ∈ A := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl a ha
    · have he : a = L.one := (List.mem_replicate.mp ha).2
      simpa only [he] using hA
  obtain ⟨x,hx⟩ := h v hvlen hva
  obtain ⟨u,_,hu,_,_⟩ := hx.split_allow_empty L rfl
  exact ⟨u,hu⟩
end LocalGroupAlgebra
end DirectedCycles
