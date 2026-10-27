module

public import DirectedCycles.LocalProductInversion
public import DirectedCycles.LocalUltraproductDomain

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Values of fully defined words of exactly n letters from A. -/
def wordPower (A : Set G) (n : ℕ) : Set G :=
  {x | ∃ l : List G, l.length = n ∧ (∀ a ∈ l, a ∈ A) ∧ L.Product l x}

/-- Every word of length at most N in A has all bracketings defined. -/
def AllProductsDefined (A : Set G) (N : ℕ) : Prop :=
  ∀ l : List G, l.length ≤ N → (∀ a ∈ l, a ∈ A) → ∃ x, L.Product l x

theorem wordPower_zero (A : Set G) : L.wordPower A 0 = {L.one} := by
  ext x
  constructor
  · rintro ⟨l,hlen,_,hp⟩
    have he : l = [] := List.length_eq_zero_iff.mp hlen
    subst l
    exact (Product.nil_iff L).1 hp
  · intro hx
    exact ⟨[],rfl,by simp,hx.symm ▸ Product.nil⟩

theorem wordPower_one (A : Set G) : L.wordPower A 1 = A := by
  ext x
  constructor
  · rintro ⟨l,hlen,ha,hp⟩
    obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hlen
    have he : x = a := (Product.singleton_iff L).1 hp
    exact he.symm ▸ ha a (by simp)
  · intro hx
    exact ⟨[x],rfl,by simpa using hx,Product.singleton x⟩

theorem Product.split_allow_empty {l a b : List G} {x : G} (h : L.Product l x)
    (he : l = a++b) : ∃ u v : G, L.Product a u ∧ L.Product b v ∧ L.mulRel u v x := by
  by_cases ha : a = []
  · subst a
    simp only [List.nil_append] at he
    exact ⟨L.one,x,Product.nil,he ▸ h,L.one_mul x⟩
  by_cases hb : b = []
  · subst b
    simp only [List.append_nil] at he
    exact ⟨x,L.one,he ▸ h,Product.nil,L.mul_one x⟩
  exact h.split L he ha hb

/-- When the concatenated word is known to be fully defined, its two given
subproducts multiply to its unique value. -/
theorem Product.append_of_defined {a b : List G} {x y : G}
    (ha : L.Product a x) (hb : L.Product b y) (hdef : ∃ z, L.Product (a++b) z) :
    ∃ z, L.Product (a++b) z ∧ L.mulRel x y z := by
  obtain ⟨z,hz⟩ := hdef
  obtain ⟨u,v,hu,hv,hm⟩ := hz.split_allow_empty L rfl
  have he : u = x := hu.unique L ha
  have he' : v = y := hv.unique L hb
  exact ⟨z,hz,by simpa only [he,he'] using hm⟩

theorem wordPower_add_subset (A : Set G) (m n : ℕ) :
    L.wordPower A (m+n) ⊆ L.setMul (L.wordPower A m) (L.wordPower A n) := by
  rintro x ⟨l,hlen,hl,hp⟩
  obtain ⟨u,v,hu,hv,hm⟩ := hp.split_allow_empty L (List.take_append_drop m l).symm
  refine ⟨u,⟨l.take m,?_,?_,hu⟩,v,⟨l.drop m,?_,?_,hv⟩,hm⟩
  · simp only [List.length_take,hlen]
    omega
  · exact fun a ha => hl a (List.mem_of_mem_take ha)
  · simp only [List.length_drop,hlen]
    omega
  · exact fun a ha => hl a (List.mem_of_mem_drop ha)

/-- Set multiplication and word addition agree within the proved domain of
all-bracketings products. -/
theorem wordPower_add {A : Set G} {N m n : ℕ} (hdef : L.AllProductsDefined A N)
    (hmn : m+n ≤ N) :
    L.wordPower A (m+n) = L.setMul (L.wordPower A m) (L.wordPower A n) := by
  apply Set.Subset.antisymm (L.wordPower_add_subset A m n)
  rintro z ⟨x,⟨a,hal,ha,hpa⟩,y,⟨b,hbl,hb,hpb⟩,hm⟩
  have hablen : (a++b).length ≤ N := by simpa only [List.length_append,hal,hbl] using hmn
  have habmem : ∀ g ∈ a++b, g ∈ A := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ha g hg
    · exact hb g hg
  obtain ⟨w,hw,hmw⟩ := hpa.append_of_defined L hpb (hdef _ hablen habmem)
  have he : w = z := L.unique hmw hm
  exact ⟨a++b,by simp only [List.length_append,hal,hbl],habmem,he ▸ hw⟩

/-- Reversing and inverting a fully defined word stays in the same power of a
symmetric set. -/
theorem inv_mem_wordPower (hL : L.Reversible) {A : Set G}
    (hi : ∀ a ∈ A, L.inv a ∈ A) {n : ℕ} {x : G} (hx : x ∈ L.wordPower A n) :
    L.inv x ∈ L.wordPower A n := by
  obtain ⟨l,hlen,hl,hp⟩ := hx
  refine ⟨l.reverse.map L.inv,?_,?_,?_⟩
  · simpa only [List.length_map,List.length_reverse] using hlen
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hi b (hl b (List.mem_reverse.mp hb))
  · exact hp.reverse_inv L hL
end LocalGroupAlgebra
end DirectedCycles
